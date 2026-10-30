-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_joining_lists_and_fibers_convex
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.joining_lists_and_fibers_convex
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T14:01:41.309917+00:00
-- url     : https://prove2.me/theorems/271180d1-b211-4c49-8928-d31fe8403e5e
-- title:
--   Sec. II A, unnumbered: convexity of compatible lists and extension fibers
-- statement:
--   Fix finitely many finite-dimensional complex tensor factors, each of positive dimension, and any finite list of neighborhoods. A marginal list is attainable if one density operator reduces to all its prescribed neighborhood states. Then
--   $$\{\text{attainable marginal lists}\}\text{ is convex},\qquad \{w:w\text{ joins a fixed list}\}\text{ is convex}.$$
--   Convex combinations of lists are componentwise; partial traces are over the exact tensor complements. Empty lists and empty neighborhoods are permitted and cause no missing normalization constraint.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 3, Sec. II A, unnumbered: convexity of compatible lists and extension fibers

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.II A, PDF p.3: convexity of attainable marginal lists and of every extension fiber. -/
theorem joining_lists_and_fibers_convex (N q : ℕ) (dim : Fin N → ℕ)
    (hdim : ∀ i, 0 < dim i) (S : Fin q → Finset (Fin N)) :
    Convex ℝ {rho : (j : Fin q) → Op (NeighborhoodConfiguration dim (S j)) | ∃ X, JoiningList dim S rho X} ∧
    (∀ rho : (j : Fin q) → Op (NeighborhoodConfiguration dim (S j)),
      Convex ℝ {X | JoiningList dim S rho X}) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
