-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedRefinement_finset_sup
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedRefinement.finset_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:18:58.477261+00:00
-- url     : https://prove2.me/theorems/b6f95a7e-3147-44fa-a4ab-1385b015d279
-- title:
--   Place Normalized Refinement: finset sup
-- statement:
--   A finite family of whole normalized chains over the same original
--   base gives a normalized chain to its literal compositum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceRefinement.lean#L101-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceRefinement.lean#L101-L114

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedRefinement.finset_sup
    [Finite Q.residueField] {ι : Type*} (s : Finset ι)
    (L : ι → IntermediateField F E)
    (h : ∀ i ∈ s, PlaceNormalizedRefinement F Q ⊥ (L i)) :
    PlaceNormalizedRefinement F Q ⊥ (s.sup L) := by sorry
