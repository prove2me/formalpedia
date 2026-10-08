-- Prove2me | Theorems.Thm_SmallGainISS_Lyapunov_decrease_5_9
-- name    : SmallGainISS.Lyapunov.decrease_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:10:39.055068+00:00
-- url     : https://prove2.me/theorems/0f1ff96f-f696-4b58-a728-0b019b55b169
-- title:
--   (5.9): one positive definite $\alpha$ with $\langle\zeta,f_i(x,u)\rangle\le-\alpha(\|x\|)$ on $\partial[\sigma_i^{-1}\circ V_i](x_i)$, $i$ active
-- statement:
--   Assume the hypotheses of Theorem 5.3: each $V_i$ is an ISS Lyapunov function for $\Sigma_i$ with gains $\Gamma$ ($\gamma_{ii}\equiv0$), $\gamma_{iu}$ and MAFs $\mu_i$, compatible as in Remark 2.6; $\sigma$ is an Ω-path with respect to $\Gamma_\mu$; $\varphi\in\mathcal K_\infty$ satisfies (5.3) $\overline\Gamma_\mu(\sigma(r),\varphi(r))<\sigma(r)$ for all $r>0$; each $f_i$ is continuous. Then there is a positive definite $\alpha$ such that for all $x\ne0$, all $u$ with $V(x)\ge\varphi^{-1}(\|u\|)$, every active index $i$ ($V(x)=\sigma_i^{-1}(V_i(x_i))$) and every $\zeta\in\partial[\sigma_i^{-1}\circ V_i](x_i)$,
--   $$\langle\zeta,f_i(x,u)\rangle\le-\alpha(\|x\|).\tag{5.9}$$
--
--   The right-hand side depends on the whole state $x$, not only on $x_i$; combined with (5.7) this gives the decrease of $V$.
--
--   **Formalization Note** $\alpha$ is chosen once, before $x$, $u$ and $i$. The trigger is the corrected $V(x)\ge\varphi^{-1}(\|u\|)$ (see the statement of Theorem 5.3 in this mission). Continuity of the $f_i$ is the regularity behind (2.6).
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 15, proof of Theorem 5.3, (5.9)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_SmallGainISS_Lyapunov_Network

open scoped NNReal

namespace SmallGainISS.Lyapunov

/-- (5.9) (p. 15): under the hypotheses of Theorem 5.3 (with the corrected trigger
`V(x) ≥ φ⁻¹(‖u‖)`), there is one positive definite `α` such that for all `x ≠ 0`, all `u`, all
active `i ∈ I` (5.6) and every `ζ ∈ ∂[σᵢ⁻¹ ∘ Vᵢ](xᵢ)`: `⟨ζ, fᵢ(x, u)⟩ ≤ −α(‖x‖)`. -/
theorem decrease_5_9 {n : ℕ} [NeZero n] {N : Fin n → ℕ} {M : ℕ}
    (Vb : (j : Fin n) → Block N j → ℝ) (f : (i : Fin n) → State N → Input M → Block N i)
    (Γ : GainMatrix n) (γu : Fin n → ℝ≥0 → ℝ≥0) (μ : Fin n → (Fin (n + 1) → ℝ≥0) → ℝ≥0)
    (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0) (φ φinv : ℝ≥0 → ℝ≥0)
    (hV : ∀ i, IsISSLyapunovSub Vb f Γ γu μ i)
    (hdiag : ZeroDiagonal Γ) (hcomp : Compatible Γ μ)
    (hσ : IsOmegaPath (gainOp Γ γu μ) σ τ)
    (hφ : IsKInf φ) (hφinv : IsInverse φinv φ)
    (h53 : ∀ r : ℝ≥0, 0 < r → SLt (gainOpBar Γ γu μ (σ r) (φ r)) (σ r))
    (hf : ∀ i, Continuous (fun p : State N × Input M => f i p.1 p.2)) :
    ∃ α : ℝ≥0 → ℝ≥0, IsPosDef α ∧
      ∀ (x : State N) (u : Input M), x ≠ 0 → (φinv ‖u‖₊ : ℝ) ≤ netV Vb τ x →
        ∀ i ∈ activeSet Vb τ x,
          ∀ ζ ∈ ClarkeGradients.Shared.generalizedGradient
              (fun z => liftR (τ i) (Vb i z)) (x i),
            inner ℝ ζ (f i x u) ≤ -(α ‖x‖₊ : ℝ) := by sorry

end SmallGainISS.Lyapunov
