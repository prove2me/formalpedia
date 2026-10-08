-- Prove2me | Theorems.Thm_TimeInconsLQ_MeanVariance_lambda_identity
-- name    : TimeInconsLQ.MeanVariance.lambda_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:51.168413+00:00
-- url     : https://prove2.me/theorems/6859ee86-b840-463b-ba7c-12d772dbc4c6
-- title:
--   Proof of Theorem 5.4, p. 22 — (p, k) of (5.5), (5.7) solve the adjoint equation (5.4), Λ(s; t) in closed form, and Λ meets (3.4)
-- statement:
--   In the market of §5, let $(M,U)$ and $(\Gamma^{(2)},\gamma^{(2)})$ be the solutions of (5.8) and (5.13) in the classes of Propositions 5.1–5.2, let $X^*$ be any closed-loop solution of the wealth equation under the feedback (5.14), $u^*_s=\alpha_sX^*_s+\beta_s$, and put $\Gamma^{(3)}=\Gamma^{(2)}-\Gamma$. Fix $t\in[0,T)$ and define, for $s\in[t,T]$, (5.7)
--   $$k(s;t)=X^*_sU_s+M_su^*_s+\gamma^{(2)}_s .$$
--   Then there is a process $p(\cdot;t)$ such that
--
--   1. $(p(\cdot;t),k(\cdot;t))$ solves on $[t,T]$ the adjoint equation of (5.4),
--   $$dp(s;t)=-r_sp(s;t)\,ds+k(s;t)'\,dW_s,\qquad p(T;t)=X^*_T-E_t[X^*_T]-\mu_1X^*_t-\mu_2 ;$$
--   2. for every $s\in[t,T]$, almost surely, (5.5) holds with $N=M$:
--   $$p(s;t)=M_sX^*_s-\Gamma^{(1)}_sX^*_t+\Gamma^{(2)}_s-E_t[M_sX^*_s+\Gamma^{(3)}_s];$$
--   3. for every $s\in[t,T]$, almost surely,
--   $$\Lambda(s;t)=p(s;t)\theta_s+k(s;t)=\big(M_sX^*_s+\Gamma^{(3)}_s-E_t[M_sX^*_s+\Gamma^{(3)}_s]\big)\theta_s+\Gamma^{(1)}_s(X^*_s-X^*_t)\theta_s ;$$
--   4. $\Lambda(\cdot;t)$ satisfies condition (3.4): $E_t\int_t^T|\Lambda(s;t)|\,ds<+\infty$ and $\lim_{s\downarrow t}E_t[\Lambda(s;t)]=0$, a.s.
--
--   These are the hypotheses of the paper's sufficient condition (Theorem 3.3) for the candidate $u^*$, which is how Theorem 5.4 is concluded.
--
--   **Formalization Note.** The adjoint equation and $\Lambda$ are the general (3.1) and $\Lambda=B p+\sum_j(D^j)'k^j+Ru^*$ evaluated on the LQ instance of the mean–variance problem; they reduce to the displayed formulas. $k$ is defined pointwise by (5.7); $p$ is existential because the per-$s$ conditional expectations in (5.5) need not form a progressive process, and item 2 identifies $p$ with (5.5) version by version. Condition (3.4) is in the version-robust form of the module `Adjoint`.
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 22, proof of Theorem 5.4; (5.4) p. 15, (5.5), (5.7) p. 16, (3.4) p. 6

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_MeanVariance_Model
import Definitions.Def_TimeInconsLQ_MeanVariance_Market
import Definitions.Def_TimeInconsLQ_MeanVariance_Adjoint

namespace TimeInconsLQ.MeanVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- Proof of Theorem 5.4 (p. 22). With `(M, U)`, `(Γ⁽²⁾, γ⁽²⁾)` as in Propositions 5.1–5.2, let
`X*` solve the closed-loop wealth equation under (5.14) and `t ∈ [0, T)`. Define `k(·; t)` by (5.7).
Then there is `p(·; t)` such that
1. `(p(·; t), k(·; t))` solves the adjoint equation of (5.4) on `[t, T]`;
2. `p(s; t) = M_sX*_s − Γ⁽¹⁾_sX*_t + Γ⁽²⁾_s − E_t[M_sX*_s + Γ⁽³⁾_s]` a.s. for every `s ∈ [t, T]`
   (that is, (5.5) with `N = M`, `Γ⁽³⁾ = Γ⁽²⁾ − Γ`);
3. `Λ(s; t) = p(s; t)θ_s + k(s; t) = (M_sX*_s + Γ⁽³⁾_s − E_t[M_sX*_s + Γ⁽³⁾_s])θ_s + Γ⁽¹⁾_s(X*_s − X*_t)θ_s`
   a.s. for every `s ∈ [t, T]`;
4. `Λ(·; t)` satisfies condition (3.4). -/
theorem lambda_identity {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (mk : Market Ω d)
    (hmk : mk.Standing)
    (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (hMU : mk.Class58 M U)
    (Γ2 : ℝ≥0 → Ω → ℝ) (γ2 : ℝ≥0 → Ω → Fin d → ℝ) (hΓ : mk.Class513 M U Γ2 γ2)
    (X : ℝ≥0 → Ω → Fin 1 → ℝ) (hX : mk.mvData.IsClosedLoop (mk.alpha M U) (mk.beta M γ2) X)
    (t : ℝ≥0) (ht : t < mk.T) :
    ∃ p : ℝ≥0 → Ω → Fin 1 → ℝ,
      mk.mvData.IsFirstAdjointAt X t p (mk.kStar M U γ2 X) ∧
      (∀ s, t ≤ s → s ≤ mk.T →
        (fun ω => p s ω 0) =ᵐ[mk.P] fun ω =>
          M s ω * X s ω 0 - mk.Gam1 s * X t ω 0 + Γ2 s ω
            - (mk.P[fun ω' => M s ω' * X s ω' 0 + (Γ2 s ω' - mk.Gam s) | mk.filt t]) ω) ∧
      (∀ s, t ≤ s → s ≤ mk.T → ∀ᵐ ω ∂mk.P,
        mk.mvData.Lam (mk.uStar M U γ2 X) p (mk.kStar M U γ2 X) s ω =
          (M s ω * X s ω 0 + (Γ2 s ω - mk.Gam s)
              - (mk.P[fun ω' => M s ω' * X s ω' 0 + (Γ2 s ω' - mk.Gam s) | mk.filt t]) ω)
            • mk.θ s ω
          + (mk.Gam1 s * (X s ω 0 - X t ω 0)) • mk.θ s ω) ∧
      mk.mvData.Cond34At t (mk.mvData.Lam (mk.uStar M U γ2 X) p (mk.kStar M U γ2 X)) := by sorry

end TimeInconsLQ.MeanVariance
