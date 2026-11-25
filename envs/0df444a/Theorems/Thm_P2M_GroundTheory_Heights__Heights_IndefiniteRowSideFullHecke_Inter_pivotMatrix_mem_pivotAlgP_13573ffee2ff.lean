-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMatrix_mem_pivotAlgP_13573ffee2ff
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMatrix_mem_pivotAlgP_13573ffee2ff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:35:12.372963+00:00
-- url     : https://prove2.me/theorems/5df933e3-a743-499a-b7ca-e5c4651d8467
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Matrix mem pivot Alg P 13573ffee2ff: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Matri
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Matrix mem pivot Alg P 13573ffee2ff construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter pivot Matrix mem pivot Alg P 13573ffee2ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L76-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
variable (F : Type) [Field F] (n : ℕ)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMatrix_mem_pivotAlgP_13573ffee2ff (j : Fin (n - 1)) (r : Fin (j + 1)) (b : Fin n) :
    pivotMatrix (genMat F n) (Fin.castLE (by have := j.2; omega) r) b ∈ pivotAlgP F n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«pivotMatrix_mem_pivotAlgP» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMatrix_mem_pivotAlgP_13573ffee2ff
