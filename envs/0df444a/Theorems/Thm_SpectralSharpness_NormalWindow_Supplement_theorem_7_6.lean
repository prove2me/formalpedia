-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_7_6
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:22:38.1941+00:00
-- url     : https://prove2.me/theorems/09524f8d-3246-4c9c-b008-3d9ebc45f9ed
-- title:
--   Theorem 7.6 — depth is logarithmically cheap
-- statement:
--   The functions s̃_L are the actual iterated clamped refinements on [−1,1], for every L≥0. Networks are compositions of affine maps and coordinate ReLUs with an affine output; their depth, hidden widths and scalar parameter counts are computed from their layer data. The displayed L+1 and later L layer wordings are both retained.
--
--   Theorem 7.6 (depth is logarithmically cheap). s̃_L is computed by a ReLU network of depth
--   L + 1, width 2, and at most 9L + 6 parameters. Consequently a γ-uncertainty window of width w is
--   realised with
--   L = ⌈log₂(γ/w)⌉ layers, O(log(γ/w)) parameters, O(1) width.
--
--   $$
--   D=L+1,\qquad W=2,\qquad P\le9L+6;\qquad L=\left\lceil\log_2(\gamma/w)\right\rceil,\quad P=O(\log(\gamma/w)).
--   $$
--
--   The exact printed parameter bound is retained even at L=0. Under the explicit dense scalar-position count, a width-two hidden layer with an affine scalar output has seven positions, so the printed six-parameter endpoint presents an additional source/convention defect. No larger bound is substituted.
--
--   The logarithmic-depth consequence computes the same constructed soft step at L=⌈log₂(γ/w)⌉, rather than an unrelated network with a small uncertainty window.
--
--   Differences from the source:
--   - encoding: depth L+1, width 2 and at most 9L+6 scalar parameters → actual consecutive affine/ReLU layers with a scalar affine output and all scalar positions counted; reason: no target function or parameter certificate is built into the network definition
--   - reading: L=ceil(log₂(γ/w)) layers in the consequence, versus L+1 in the construction → retains both depth claims, with the consequence stated eventually as positive w tends to zero; reason: the source uses logarithmic resource notation; the inconsistent layer wording is exposed rather than silently changed
--   - encoding: O, o, Θ or Ω asymptotic notation → actual big-O, two-sided asymptotic bounds, limits or eventual inequalities at the stated filter; reason: quantifiers constrain the actual functions rather than an independent error term
--   - generalization: a network realizing a window of width at most w in the logarithmic-depth consequence → that network also computes the specified softStep at index ceil(log₂(γ/w)) on [−1,1]; reason: forgetting the exact-function equality recovers the full printed consequence; the extra requirement identifies the constructed classifier
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 7.6, p. 21

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Refinement

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_7_6 :
    (∀ L : ℕ, ∃ net : ReluNetwork, net.depth=L+1 ∧ net.widthAtMost 2 ∧ (∃ i ∈ Set.Icc 1 net.depth, net.widths i=2) ∧
      net.parameterCount ≤ 9*L+6 ∧ ∀ x ∈ Set.Icc (-1:ℝ) 1, net.eval x=softStep L x) ∧
    (∀ γ : ℝ, 0 < γ ∧ γ < 1 → ∃ nets : ℝ → ReluNetwork,
      (∀ᶠ w in nhdsWithin (0:ℝ) (Set.Ioi 0),
        (nets w).depth=logDepth γ w ∧ (nets w).widthAtMost 2 ∧
        (∀ x ∈ Set.Icc (-1:ℝ) 1, (nets w).eval x=softStep (logDepth γ w) x) ∧
        intervalWindow γ (nets w).eval ≤ w) ∧
      Asymptotics.IsBigO (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (fun w => ((nets w).parameterCount:ℝ)) (fun w => Real.log (γ/w))) := by sorry

end SpectralSharpness.NormalWindow.Supplement
