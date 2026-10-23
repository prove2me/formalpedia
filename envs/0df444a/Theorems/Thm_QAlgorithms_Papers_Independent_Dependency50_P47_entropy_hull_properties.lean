-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P47_entropy_hull_properties
-- name    : QAlgorithms.Papers.Independent.Dependency50.P47.entropy_hull_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:42:33.513769+00:00
-- url     : https://prove2.me/theorems/e508bf36-211e-4ce0-8f9c-945e58b0c0a7
-- title:
--   §4 unnumbered: quantum convexification is convex and includes classical convexification
-- statement:
--   Fix finite nonempty alphabets $X_1,\ldots,X_m$, and let $G$ be the graph mapping a joint probability law $p$ to its tuple of marginal entropies. Define $\operatorname{ConvHull}(G)$ by adjoining a finite classical auxiliary $C$, and define $\operatorname{QConvHull}(G)$ by adjoining any finite-dimensional quantum auxiliary $F$. In each case the hull point includes the original law and the conditional-entropy tuple. Then
--
--   $$
--   \operatorname{ConvHull}(G)\subseteq\operatorname{QConvHull}(G),
--   \qquad \operatorname{QConvHull}(G)\text{ is convex}.
--   $$
--
--   There is no closure operation or fixed auxiliary dimension. The empty list of coordinates is harmless. This structural result distinguishes quantum convexification from the later strict-separation result.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, PDF p. 9, §4 unnumbered: quantum convexification is convex and includes classical convexification

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- §4, PDF p.9: convexity and inclusion, without closure or a dimension cutoff. -/
theorem entropy_hull_properties (m : ℕ) (s : Fin m → ℕ) (hs : ∀ i, 0 < s i) :
    Convex ℝ (quantumHull m s) ∧ classicalHull m s ⊆ quantumHull m s := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P47

end
