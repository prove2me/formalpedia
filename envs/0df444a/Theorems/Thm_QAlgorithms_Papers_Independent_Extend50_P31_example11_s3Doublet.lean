-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_example11_s3Doublet
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.example11_s3Doublet
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:31:09.606354+00:00
-- url     : https://prove2.me/theorems/8643705b-39b0-456b-a5a0-d4ba07c14ae1
-- title:
--   Example 11: S(3) doublet tensor decomposition
-- statement:
--   For the two-dimensional unitary irreducible representation $U$ of $S_3$ of partition $(2,1)$, there is an invertible intertwiner implementing
--
--   $$
--   U\otimes\overline U\simeq\mathrm{id}\oplus\mathrm{sgn}\oplus U,\qquad\dim_{\mathbb C}\operatorname{Int}_{S_3}(U\otimes\overline U)=3.
--   $$
--
--   This describes the S(3) doublet tensor decomposition in the fixed source conventions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 9, Example 11: S(3) doublet tensor decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.9, Example 11 Eq.(39). The two-dimensional irrep of S3 is (2,1). -/
theorem example11_s3Doublet (U : UnitaryIrrep (Equiv.Perm (Fin 3)) 2) :
    DoubletDecomposition U ∧ Module.finrank ℂ (representationCommutant (tensorConjugate U)) = 3 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
