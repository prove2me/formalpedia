-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedExtension_compositum_left
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedExtension.compositum_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:35:39.20393+00:00
-- url     : https://prove2.me/theorems/b10c81ed-a906-4b8c-9c03-9060b1829256
-- title:
--   Place Normalized Extension: compositum left
-- statement:
--   One source-pyramid square as an actual inclusion between coordinate
--   fields. Both incoming refinements produce the outgoing refinement over
--   the left upper field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceRefinement.lean#L147-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceRefinement.lean#L147-L167

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_compositum_left
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_compositum_left

set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
variable (Q : GlobalPlace F256 E) {K L M : IntermediateField F256 E}
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [FiniteDimensional L E] [Algebra.IsSeparable L E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedExtension.compositum_left [Finite Q.residueField]
    (hL : PlaceNormalizedExtension Q K L) (hM : PlaceNormalizedExtension Q K M) :
    PlaceNormalizedExtension Q L (L ⊔ M) := by sorry
