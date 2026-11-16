-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_3_2
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:08:07.388645+00:00
-- url     : https://prove2.me/theorems/af759a46-9c93-41a6-88b8-c6bbc5375e90
-- title:
--   Theorem 3.2 — ℓ¹ is exactly the threshold for worst-case reconstruction
-- statement:
--   Let X be a compact metric space with a Borel probability μ, and let φ_j be a complete uniformly essentially bounded orthonormal basis with actual measurable representatives. Let g be an essentially bounded representative, B_j=‖φ_j‖∞, ĝ_j its coefficient and g_d its partial expansion. The oscillation is the literal representative-dependent formula from §3.1. Both real and complex scalars are covered. The following are the full printed assertions, including the final characterization.
--
--   Theorem 3.2 (ℓ¹ is exactly the threshold for worst-case reconstruction). Let g ∈ L∞(X)
--   and let (φ_j) be as above with B = sup_j B_j < ∞.
--   (a) (ℓ¹ suffices.) If ∑_{j≥0} |ĝ_j|B_j < ∞ then g_d → g uniformly, with the explicit rate ∥g − g_d∥∞ ≤ ∑_{j>d} |ĝ_j|B_j → 0.
--   (b) (a jump forces ℓ² \ ℓ¹.) If osc(g) = δ > 0 then ∑_{j≥0} |ĝ_j|B_j = ∞; and for every d and every continuous f, in particular for every f ∈ span{φ_0, . . . , φ_d},
--   ∥g − f∥_{L∞} ≥ δ/2.
--   Hence inf_{deg f≤d} sup_{g: osc(g)≥δ} ∥g − f∥∞ ≥ δ/2: no bandwidth defeats a discontinuity, in any bounded basis.
--   (c) (ℓ² always suffices on average.) For every g ∈ L², ∥g − g_d∥₂ → 0 whatever the basis.
--   So worst-case (uniform) reconstruction succeeds iff the coefficient sequence is in ℓ¹, average-case reconstruction succeeds for every ℓ² sequence, and every discontinuous target lies in the gap.
--
--   $$
--   \|g-g_d\|_\infty\le\sum_{j>d}|\widehat g_j|B_j\to0\quad\text{if }\sum_j|\widehat g_j|B_j<\infty;\qquad \|g-f\|_\infty\ge\frac\delta2\quad\text{if }\operatorname{osc}(g)=\delta>0.
--   $$
--
--   Source defect retained: a Rademacher element in the Walsh basis has positive oscillation and exactly one nonzero coefficient. Thus the printed jump and final iff assertions are not claimed to be true. No continuity assumption has been inserted to repair them.
--
--   The minimax consequence retains the preceding premise δ=osc(g)>0. Its independent average-case conclusion quantifies over every L² target, without requiring that target to be essentially bounded.
--
--   Differences from the source:
--   - encoding: bounded orthonormal basis, partial spans, essential oscillation and minimax error → measurable representatives with orthonormal L² classes and dense span; ENNReal oscillation and minimax; reason: no continuity, full support or target regularity is added; infinite values remain representable
--   - reading: every discontinuous target lies in the gap → positive printed essential oscillation implies square-summable but not absolutely summable coefficients; reason: the section defines its essential discontinuity using this oscillation, without replacing it by representative-invariant continuity
--   - generalization: an orthonormal expansion with unspecified real or complex scalar convention → RCLike scalar field with ĝ_j=∫conjugate(φ_j)g dμ; reason: specializing the scalar field to either conventional source choice recovers that entire case, with the standard expansion coefficient
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 3.2, p. 9

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Expansions

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- Literal printed assertions, including the documented false bounded-basis jump claim. -/
theorem theorem_3_2 {𝕜 X : Type*} [RCLike 𝕜] [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (b : BoundedBasis 𝕜 X μ) (g : X → 𝕜) (hg : MemLp g ⊤ μ) :
  (Summable (weightedAbsolute b g) →
    TendstoUniformly (partialExpansion b g) g atTop ∧
    (∀ d, eLpNorm (fun x => g x-partialExpansion b g d x) ⊤ μ ≤
      ∑' j : ℕ, if d < j then ENNReal.ofReal (weightedAbsolute b g j) else 0) ∧
    Tendsto (fun d => ∑' j : ℕ, if d < j then weightedAbsolute b g j else 0)
      atTop (nhds 0)) ∧
  (∀ δ : ℝ, 0 < δ → essentialOscillation μ g=ENNReal.ofReal δ →
    ¬ Summable (weightedAbsolute b g) ∧
    (∀ (f : X → 𝕜), Continuous f →
      ENNReal.ofReal (δ/2) ≤ eLpNorm (fun x => g x-f x) ⊤ μ) ∧
    (∀ d (f : X → 𝕜), inPartialSpan b d f →
      ENNReal.ofReal (δ/2) ≤ eLpNorm (fun x => g x-f x) ⊤ μ)) ∧
  (∀ δ : ℝ, 0 < δ → essentialOscillation μ g=ENNReal.ofReal δ →
    ∀ d, ENNReal.ofReal (δ/2) ≤ reconstructionMinimax b d δ) ∧
  (∀ h : X → 𝕜, MemLp h 2 μ →
    Tendsto (fun d => eLpNorm (fun x => h x-partialExpansion b h d x) 2 μ) atTop (nhds 0)) ∧
  (TendstoUniformly (partialExpansion b g) g atTop ↔
    Summable (fun j => ‖coefficient b g j‖)) ∧
  (0 < essentialOscillation μ g →
    Summable (fun j => ‖coefficient b g j‖^2) ∧ ¬ Summable (fun j => ‖coefficient b g j‖)) := by sorry

end SpectralSharpness.NormalWindow.Supplement
