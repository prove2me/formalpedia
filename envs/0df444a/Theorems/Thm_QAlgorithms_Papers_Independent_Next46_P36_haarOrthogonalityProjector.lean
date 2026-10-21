-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_haarOrthogonalityProjector
-- name    : QAlgorithms.Papers.Independent.Next46.P36.haarOrthogonalityProjector
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:45:46.229983+00:00
-- url     : https://prove2.me/theorems/18d5d0ea-66ac-4c49-a6ef-5c937437f9b4
-- title:
--   Proposition 1: Haar orthogonality projector
-- statement:
--   Let $G$ be a compact group with normalized two-sided Haar measure, and let $U^\mu$ be pairwise inequivalent positive-dimensional based continuous unitary irreducible representations. Then
--
--   $$\int_G U_g^\mu\otimes\overline{U_g^\mu}\,dg=\frac{|\operatorname{vec}(I_\mu)\rangle\langle\operatorname{vec}(I_\mu)|}{d_\mu},\qquad \int_G U_g^\mu\otimes\overline{U_g^\nu}\,dg=0\quad(\mu\ne\nu).$$
--
--   The unequal-label integral is zero on $H_\mu\otimes H_\nu$; no ill-typed Kronecker-delta expression is used. The bar is entrywise complex conjugation, not adjoint. This gives the invariant rank-one projector, including value one for the trivial one-dimensional irrep.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 10, Appendix Proposition 1, Eq. (69)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.10 Proposition 1 Eq.(69): equal labels give the normalized invariant
rank-one projector; unequal labels give zero on their own correctly typed space.
The star in the source is entrywise conjugation, not adjoint. -/
theorem haarOrthogonalityProjector
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {S : Type*} (D : S → BasedIrrep G) (hD : OccurringIrrepsInequivalent D)
    (dg : Measure G) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg] :
    (∀ s, (∫ g, (D s).matrix g ⊗ₖ ((D s).matrix g).map conj ∂dg) =
      ((D s).dim : ℂ)⁻¹ • QAlgorithms.pureDensity (irrepVectorization (1 : Matrix (Fin (D s).dim) _ ℂ))) ∧
    (∀ s t, s ≠ t → (∫ g, (D s).matrix g ⊗ₖ ((D t).matrix g).map conj ∂dg) = 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
