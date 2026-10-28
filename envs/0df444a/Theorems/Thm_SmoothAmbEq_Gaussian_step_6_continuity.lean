-- Prove2me | Theorems.Thm_SmoothAmbEq_Gaussian_step_6_continuity
-- name    : SmoothAmbEq.Gaussian.step_6_continuity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:37.308153+00:00
-- url     : https://prove2.me/theorems/d2d48379-8247-4909-84bd-76b6452ec3fc
-- title:
--   Appendix G, Step 6, p. 43, (G.5) — lim_{h→0+} E[g^z(t+h, X^{z,π}_{t+h}, β^z_{t+h})] = g^z(t, x, β)
-- statement:
--   Assume the hypotheses of Theorem 5.5. Let $\pi\in\Pi$, $(t,x,\beta)\in[0,T)\times\mathbb R^2$ and $z\in\mathbb R$. For the inside system started at $X_t=x$, $\beta^z_t=\beta$,
--   $$\lim_{h\to0^+}\mathbb E\big[g^z(t+h,X^{z,\pi}_{t+h},\beta^z_{t+h})\mid X^{z,\pi}_t=x,\beta^z_t=\beta\big]=g^z(t,x,\beta).\qquad(G.5)$$
--
--   This is the Gaussian instance of Assumption 4.4: the candidate value is continuous along every admissible deviation over a vanishing time.
--
--   **Formalization Note** The conditional expectation is the expectation for the system started at $(t,x,\beta)$. The expectations are stated to be finite for all small $h>0$, so the limit is not taken over default values.
-- source:
--   Guan, Liang, Xia, Equilibrium Portfolio Selection for Smooth Ambiguity Preferences, arXiv:2302.08181v1, p. 43, Appendix G, Step 6, (G.5)

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbEq.Gaussian

/-- Appendix G, Step 6, p. 42, (G.5). Under the hypotheses of Theorem 5.5, let `π ∈ Π`,
`(t, x, β) ∈ [0, T) × ℝ²` and `z ∈ ℝ`. For the wealth started at `(t, x, β)`,
`lim_{h → 0+} E[g^z(t + h, X^{z,π}_{t+h}, β^z_{t+h})] = g^z(t, x, β)` (the expectations being finite
for small `h`). -/
theorem step_6_continuity (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (π : Strategy) (hπ : Admissible M P W π) (t : ℝ) (ht : t ∈ Ico 0 M.T) (x β z : ℝ)
    (X : ℝ → Ω → ℝ) (hX : IsInsideWealth M P W π z t x β X) :
    (∀ᶠ h in 𝓝[>] (0 : ℝ), Integrable
      (fun ω => gz M c z (t + h) (X (t + h) ω) (betaZ M W z t β (t + h) ω)) P) ∧
    Tendsto (fun h => ∫ ω, gz M c z (t + h) (X (t + h) ω) (betaZ M W z t β (t + h) ω) ∂P)
      (𝓝[>] 0) (𝓝 (gz M c z t x β)) := by sorry

end SmoothAmbEq.Gaussian
