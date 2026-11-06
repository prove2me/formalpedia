-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier16_regularRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.artinSchreier16_regularRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:53.734194+00:00
-- url     : https://prove2.me/theorems/723a66ef-4940-4fc5-90fb-1ad1ffd8e380
-- title:
--   F256 Garcia Stichtenoth: artin Schreier16 regular Refinement
-- statement:
--   The four actual trace coordinates give a regular refinement of an
--   additive degree-sixteen equation. Redundant stages are permitted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L85-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinement.lean#L85-L103

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.artinSchreier16_regularRefinement [CharP E 2]
    (K : IntermediateField F E) (y : E)
    (hy : y ∈ Q.valuationRing) (ha : y ^ 16 + y ∈ K) :
    RegularRefinement Q K (K ⊔ F⟮y⟯) := by sorry
