-- Prove2me | Theorems.Thm_SeqExpDiffusion_proposition_7_single_crossing
-- name    : SeqExpDiffusion.proposition_7_single_crossing
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:23.623229+00:00
-- url     : https://prove2.me/theorems/2c1bd28e-f899-47a9-85ff-54073c88e69e
-- title:
--   Proof of Proposition 7, p.52 — two continuation-region solutions cross at most once
-- statement:
--   Let $r>0$, $\tilde\sigma>0$ and $\gamma=(1+\sqrt{1+8r/\tilde\sigma^2})/2$. If $(C^0,C^1)\ne(D^0,D^1)$, then the functions
--
--   $$C^0(1-\delta)^\gamma\delta^{1-\gamma}+C^1(1-\delta)^{1-\gamma}\delta^\gamma\qquad\text{and}\qquad D^0(1-\delta)^\gamma\delta^{1-\gamma}+D^1(1-\delta)^{1-\gamma}\delta^\gamma$$
--
--   agree at no more than one point of $(0,1)$.
--
--   The proof of Proposition 7 uses this to show that the two-action values cross finitely often, so that the exceptional set of $\tilde V$ is finite.
--
--   Differences from the source:
--   - reading: "can only cross at most once" → agree at most at one point of (0, 1), for different constant pairs; reason: equal constants give the same function, which agrees everywhere; the page compares different pairs of actions
--   - generalization: in the continuation regions → on all of (0, 1); reason: the continuation regions are subsets of (0, 1), so the statement specializes to the page
--   - encoding: r and σ̃ are a discount rate and a volatility, with no stated sign → r > 0 and σ̃ > 0; reason: the paper uses both silently (γ needs σ̃ ≠ 0, and r = 0 gives γ = 1); only degenerate cases are excluded
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, proof of Proposition 7, p.52

import Definitions.Def_SeqExpDiffusion_gammaOf
import Definitions.Def_SeqExpDiffusion_contValue

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- Proof of Proposition 7, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.52: "in the continuation regions the functions
`C⁰_ij (1 − δ)^γ δ^{1−γ} + C¹_ij (1 − δ)^{1−γ} δ^γ` and `C⁰_kℓ (1 − δ)^γ δ^{1−γ} + C¹_kℓ (1 − δ)^{1−γ} δ^γ`
can only cross at most once".

If the constant pairs differ, the two functions agree at no more than one point of `(0, 1)`.

**Formalization Note** The hypothesis `(C₀, C₁) ≠ (D₀, D₁)` is needed: equal constants give the same
function. `γ = gammaOf r σ`. -/
theorem proposition_7_single_crossing (r σ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (C₀ C₁ D₀ D₁ : ℝ) (hne : (C₀, C₁) ≠ (D₀, D₁)) :
    {δ ∈ Ioo (0 : ℝ) 1 |
      contValue (gammaOf r σ) C₀ C₁ δ = contValue (gammaOf r σ) D₀ D₁ δ}.Subsingleton := by sorry

end SeqExpDiffusion
