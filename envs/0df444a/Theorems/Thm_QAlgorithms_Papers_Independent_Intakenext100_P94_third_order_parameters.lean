-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_third_order_parameters
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.third_order_parameters
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:45:00.464989+00:00
-- url     : https://prove2.me/theorems/893f5677-8d86-4d01-a30c-b89742254ebe
-- title:
--   Third-order equality strata and 203 linear parameters
-- statement:
--   Let $n\ge6$ and order the seven shapes as $(n),(n-1,1),(n-2,2),(n-2,1,1),(n-3,3),(n-3,2,1),(n-3,1,1,1)$. In the full real order-three tensor representation, split the coordinates into pairwise distinct indices, three exactly-two-equal patterns, and all-equal indices. Their respective multiplicity vectors are $(1,3,3,3,1,2,1)$, $(1,2,1,1,0,0,0)$ for each of the three middle strata, and $(1,1,0,0,0,0,0)$. Consequently the full type is $(5,10,6,6,1,2,1)$ and
--
--   $$
--   \dim_{\mathbb R}\operatorname{End}_{S_n}(\mathbb R^{n\times n\times n})=5^2+10^2+6^2+6^2+1^2+2^2+1^2=203.
--   $$
--
--   Each type is an actual equivariant linear isomorphism to copies of concrete real Specht modules. The count concerns the linear operation before any nonlinearity.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 15, §10.1 (Appendix C): third order decomposition and 203 parameters

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Appendix C §10.1, source PDF p.15: all five equality strata, full type and
203-dimensional space of linear layers. Stable range n≥6 is explicit; the
printed count fails for small n. The dimensions count maps, never scalar evaluations. -/
theorem third_order_parameters (n : ℕ) (hn : 6 ≤ n)
    (lambda : Fin 7 → QAlgorithms.Schur.Partition n n)
    (hshape : ∀ a, (lambda a).val.rowLens = thirdShapes n a) :
    HasTensorType (DistinctSpace n 3) lambda ![1,3,3,3,1,2,1] ∧
    (∀ a : Fin 3, HasTensorType (supportedSpace (pairPattern a)) lambda ![1,2,1,1,0,0,0]) ∧
    HasTensorType (supportedSpace (fun t : Fin 3 → Fin n => ∀ a b, t a = t b))
      lambda ![1,1,0,0,0,0,0] ∧
    HasTensorType (⊤ : Submodule ℝ (Tensor n 3)) lambda ![5,10,6,6,1,2,1] ∧
    Module.finrank ℝ (equivariantLinearMaps (permutationTensorAction (n := n) (k := 3))
      (permutationTensorAction (n := n) (k := 3))) = 203 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
