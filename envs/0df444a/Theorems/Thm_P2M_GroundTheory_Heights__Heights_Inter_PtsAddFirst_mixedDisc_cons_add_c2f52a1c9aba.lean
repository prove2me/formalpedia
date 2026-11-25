-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_mixedDisc_cons_add_c2f52a1c9aba
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_mixedDisc_cons_add_c2f52a1c9aba
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:42:20.763818+00:00
-- url     : https://prove2.me/theorems/a17b52b3-bff7-4a4c-81d4-1bbd4a3e6e36
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pts Add First mixed Disc cons add c2f52a1c9aba: P2 M Ground Theory Heights  Heights Inter Pts Add First mixed Disc cons add c2f52a1c9aba
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pts Add First mixed Disc cons add c2f52a1c9aba construction uses the P2 M Ground Theory Heights  Heights Inter Pts Add First mixed Disc cons add c2f52a1c9aba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPtsAddFirst.lean#L34-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_mixedDisc_cons_add_c2f52a1c9aba {D : ℕ} (A B : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (C : Fin D → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) :
    mixedDisc (Fin.cons (A + B) C : Fin (D + 1) → _) =
      mixedDisc (Fin.cons A C : Fin (D + 1) → _) + mixedDisc (Fin.cons B C : Fin (D + 1) → _) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PtsAddFirst».«mixedDisc_cons_add» := P2M_GroundTheory_Heights__Heights_Inter_PtsAddFirst_mixedDisc_cons_add_c2f52a1c9aba
