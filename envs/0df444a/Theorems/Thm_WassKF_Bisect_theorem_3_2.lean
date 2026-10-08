-- Prove2me | Theorems.Thm_WassKF_Bisect_theorem_3_2
-- name    : WassKF.Bisect.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:12:44.306981+00:00
-- url     : https://prove2.me/theorems/48a735cc-fa6f-4bf0-8f5d-10a1a13c06f5
-- title:
--   Theorem 3.2 (Direction-finding subproblem), p. 5 — Algorithm 1 outputs a feasible and ε-suboptimal solution to (7b)
-- statement:
--   Let $d = n + m$ with $n \ge 1$, let $\rho, \varepsilon > 0$, $\Sigma \in \mathbb{S}^d_{++}$ and $S \in \mathbb{S}^d_+$, and let $\underline{\sigma} = \lambda_{\min}(\Sigma)$. Put $D = \nabla f(S) = [I_n, -G]^\top[I_n, -G]$ with $G = S_{xy}S_{yy}^{-1}$, let $\lambda_1$ be the largest eigenvalue of $D$ and $v_1$ an eigenvector of $\lambda_1$ with $\|v_1\| = 1$. The direction-finding subproblem (7b) is
--   $$
--   \max_{L \succeq \underline\sigma I_d}\ \langle L, D\rangle \quad\text{s.t.}\quad \mathrm{Tr}\Big[L + \Sigma - 2\big(\Sigma^{1/2}L\Sigma^{1/2}\big)^{1/2}\Big] \le \rho^2 ,
--   $$
--   with $\langle A, B\rangle = \mathrm{Tr}[A^\top B]$; let $\mathcal F$ be its feasible set. Run Algorithm 1 on $(\Sigma, D, \rho, \varepsilon)$: pass $k$ tries $\gamma_k = (UB_k + LB_k)/2$, starting from $[LB_0, UB_0] = [\gamma_{\min}, \gamma_{\max}]$, and the loop exits after pass $k$ with output $L(\gamma_k) = \gamma_k^2(\gamma_k I_d - D)^{-1}\Sigma(\gamma_k I_d - D)^{-1}$ when $h(\gamma_k) > 0$ and $\Delta(\gamma_k) < \varepsilon$. Then:
--
--   1. **(Soundness.)** At every pass $k$ at which the exit test holds,
--   $$
--   L(\gamma_k) \in \mathcal F \qquad\text{and}\qquad \langle L', D\rangle \le \langle L(\gamma_k), D\rangle + \varepsilon \quad\text{for all } L' \in \mathcal F .
--   $$
--   2. **(Termination.)** If $h$ does not vanish at any dyadic point $\gamma_{\min} + j(\gamma_{\max} - \gamma_{\min})/2^k$ with $k \ge 0$ and $0 < j \le 2^k$, then the exit test holds at some pass $k$.
--
--   Together these say that Algorithm 1 outputs a feasible and $\varepsilon$-suboptimal solution of (7b). This is the guarantee that makes Algorithm 1 a valid linear-minimization oracle inside the Frank–Wolfe method (Algorithm 2) for program (5).
--
--   **Added hypotheses (corrections to the printed theorem).** (i) The termination hypothesis in 2: the printed theorem implicitly claims that the loop terminates, which fails when a trial point $\gamma_k$ (or $\gamma_{\max}$) is exactly the root $\gamma^\star$ of $h$: the else-branch then sets $UB = \gamma^\star$, every later trial point lies below $\gamma^\star$ where $h < 0$, and the test $h(\gamma) > 0$ never holds. Soundness needs no such hypothesis. (ii) $\|v_1\| = 1$: the page says only "an eigenvector", and $\gamma_{\min}$ is wrong for a rescaled one. (iii) $n \ge 1$, which makes $D \neq 0$ (Lemmas A.1–A.3 assume $D \in \mathbb{S}^d_+ \setminus\{0\}$); for $n = 0$ the algorithm can return $L = 0 \notin \mathcal F$.
--
--   **Formalization Note** $\mathcal F$ is `WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Σ σ`; $\underline\sigma$ is passed as $\sigma$ with $\Sigma - \sigma I_d \succeq 0$ and an eigenvector, $\lambda_1$ as `lam1` with $\lambda_1 I_d - D \succeq 0$ and $Dv_1 = \lambda_1 v_1$. The algorithm is modelled as its sequence of passes (`bisectState`, `bisectGamma`, `bisectOutput`, `bisectStops`), so the output is $L(\gamma_k)$ at the first pass whose exit test holds, and soundness is stated for every such pass. $\varepsilon$-suboptimality is stated with a universal quantifier over $\mathcal F$, not with a supremum. Mathlib's inverse makes $S_{yy}^{-1} = 0$ when $S_{yy}$ is singular, as allowed by $S \in \mathbb{S}^d_+$; $D$ is then $\mathrm{diag}(I_n, 0)$.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 5, Theorem 3.2; p. 6, Algorithm 1; p. 13, App. A.3

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet
import Definitions.Def_WassKF_Bisect_gradF
import Definitions.Def_WassKF_Bisect_hFun
import Definitions.Def_WassKF_Bisect_Lgamma
import Definitions.Def_WassKF_Bisect_Delta
import Definitions.Def_WassKF_Bisect_algorithm1

open Matrix

namespace WassKF.Bisect

/-- Theorem 3.2 (Direction-finding subproblem), p. 5: for `ρ, ε > 0`, `Σ ≻ 0` and `S ⪰ 0`,
Algorithm 1 run on `D = ∇f(S)` (`gradF S`), with `λ₁` the largest eigenvalue of `D` and `v₁` a
unit eigenvector for it, outputs a feasible and `ε`-suboptimal solution of (7b), whose feasible
set is `sdpFeasibleSet ρ Σ σ̲` with `σ̲ = λ_min(Σ)` passed as `σ`.
(1) Soundness: at every pass `k` at which the exit test `h(γ) > 0 ∧ Δ < ε` holds, the matrix `L`
of that pass is feasible and within `ε` of every feasible objective value `⟨L', D⟩ = Tr[L'ᵀD]`.
(2) Termination: the exit test holds at some pass, provided `h` has no root at a dyadic point
`γ_min + j(γ_max − γ_min)/2^k`, `0 < j ≤ 2^k` (added hypothesis: otherwise the loop can run forever).
Added: `0 < n` (so `D ≠ 0`) and `v₁ᵀv₁ = 1`. -/
theorem theorem_3_2 {n m : ℕ} (hn : 0 < n)
    (Sigma S : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) (ρ ε σ lam1 : ℝ)
    (v₁ : Fin n ⊕ Fin m → ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) (hSigma : Sigma.PosDef) (hS : S.PosSemidef)
    (hσ : (Sigma - σ • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)).PosSemidef)
    (hσ_eig : ∃ v : Fin n ⊕ Fin m → ℝ, v ≠ 0 ∧ Sigma *ᵥ v = σ • v)
    (hlam : (lam1 • (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ) - gradF S).PosSemidef)
    (hv : gradF S *ᵥ v₁ = lam1 • v₁) (hv1 : v₁ ⬝ᵥ v₁ = 1) :
    (∀ k : ℕ, bisectStops Sigma (gradF S) ρ ε lam1 v₁ k →
        bisectOutput Sigma (gradF S) ρ lam1 v₁ k ∈
            WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ ∧
          ∀ L' ∈ WassersteinDRO.Shrinkage.sdpFeasibleSet ρ Sigma σ,
            (L'ᵀ * gradF S).trace ≤
              ((bisectOutput Sigma (gradF S) ρ lam1 v₁ k)ᵀ * gradF S).trace + ε) ∧
      ((∀ k j : ℕ, 0 < j → j ≤ 2 ^ k →
          hFun Sigma (gradF S) ρ
              (gammaMin Sigma ρ lam1 v₁ +
                (j : ℝ) * (gammaMax Sigma ρ lam1 - gammaMin Sigma ρ lam1 v₁) / 2 ^ k) ≠ 0) →
        ∃ k : ℕ, bisectStops Sigma (gradF S) ρ ε lam1 v₁ k) := by sorry

end WassKF.Bisect
