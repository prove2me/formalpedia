-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_isIso___coindSES_f3a87d3de945
-- name    : P2M_GroundTheory_GroupCoh_isIso___coindSES_f3a87d3de945
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:51.363112+00:00
-- url     : https://prove2.me/theorems/8345c254-5fdb-45de-84a0-bc0d0a6636f6
-- title:
--   P2 M Ground Theory Group Coh is Iso   coind SES f3a87d3de945: P2 M Ground Theory Group Coh is Iso   coind SES f3a87d3de945
-- statement:
--   The P2 M Ground Theory Group Coh is Iso   coind SES f3a87d3de945 construction uses the P2 M Ground Theory Group Coh is Iso   coind SES f3a87d3de945 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DimensionShift.lean#L96-L98

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]

theorem P2M_GroundTheory_GroupCoh_isIso___coindSES_f3a87d3de945 (A : Rep.{u} k G) (n : ℤ) :
    IsIso (TateCohomology.δ (coindSES_shortExact A) n) := by sorry

alias «GroundTheory».«GroupCoh».«isIso_δ_coindSES» := P2M_GroundTheory_GroupCoh_isIso___coindSES_f3a87d3de945
