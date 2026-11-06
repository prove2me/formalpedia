-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedRefinement_compositum
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedRefinement.compositum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:36:45.299078+00:00
-- url     : https://prove2.me/theorems/12d1da17-aae6-4997-b204-f2d83e5fa094
-- title:
--   Place Normalized Refinement: compositum
-- statement:
--   Sweep the finite quadratic grid at the actual ambient place. Residue
--   finiteness at its base is derived from the ambient residue field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceRefinement.lean#L75-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceRefinement.lean#L75-L84

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_compositum
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_compositum

set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E]
    [Algebra F256 F] [Algebra F256 E] [Algebra F E] [IsScalarTower F256 F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace F256 E)

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedRefinement.compositum
    [Finite Q.residueField] {J L M : IntermediateField F E}
    (hL : PlaceNormalizedRefinement F Q J L)
    (hM : PlaceNormalizedRefinement F Q J M) :
    PlaceNormalizedRefinement F Q L (L ⊔ M) ∧
      PlaceNormalizedRefinement F Q M (L ⊔ M) := by sorry
