-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_embeddedSourceW_regularRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.embeddedSourceW_regularRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:35:46.599817+00:00
-- url     : https://prove2.me/theorems/9921c9af-2031-42bf-96dd-ef75bc5198a7
-- title:
--   F256 Garcia Stichtenoth: embedded Source W regular Refinement
-- statement:
--   A regular actual image of w gives a regular refinement through the
--   whole embedded source field, without assuming a chain or an index formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularSourceRefinement.lean#L57-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularSourceRefinement.lean#L57-L72

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRegularCoordinates
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularSourceRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {E : Type*} [_root_.Field E] [Algebra F256 E]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.embeddedSourceW_regularRefinement (m : ℕ) (f : SourceField m →ₐ[F256] E)
    (Q : GlobalPlace F256 E) (K : IntermediateField F256 E)
    (hK : f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW) ∈ K)
    (hw : Q.valuation (f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)) = 1) :
    RegularRefinement Q K (K ⊔ f.fieldRange) := by sorry
