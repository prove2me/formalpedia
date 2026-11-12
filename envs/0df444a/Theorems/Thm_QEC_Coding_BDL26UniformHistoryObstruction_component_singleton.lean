-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_component_singleton
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.component_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:08:22.940849+00:00
-- url     : https://prove2.me/theorems/34a5836e-6a82-4347-ab5e-fe8c3087ed3e
-- title:
--   BDL26 Uniform History Obstruction: component singleton
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the component singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L56-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L56-L68

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.component_singleton (S : OddScale) (j : Nat) (lower : Finset (StrictLowerNode S j))
    (p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    component S j lower p hp = {BDL26UniformTopOwnerIsolation.topNode S (2 * j + 3) (topOwner S j p)} := by sorry
