-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_leadMinor_mem_pivotAlgP_593e98f45199
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_leadMinor_mem_pivotAlgP_593e98f45199
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:02.316284+00:00
-- url     : https://prove2.me/theorems/26bde82e-dde6-5da1-964b-899ac65eebec
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter lead Minor mem pivot Alg P 593e98f45199: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter lead Minor me
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter lead Minor mem pivot Alg P 593e98f45199 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter lead Minor mem pivot Alg P 593e98f45199 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean#L73-L74

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_leadMinor_mem_pivotAlgP_593e98f45199 (a : Fin (n - 1)) : leadMinor (genMat F n) a ∈ pivotAlgP F n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«leadMinor_mem_pivotAlgP» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_leadMinor_mem_pivotAlgP_593e98f45199
