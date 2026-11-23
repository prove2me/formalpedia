-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_relIndex_sup_of_le_normalizer_7514b13ff881
-- name    : P2M_GroundTheory_Variant__N1_relIndex_sup_of_le_normalizer_7514b13ff881
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:39.804328+00:00
-- url     : https://prove2.me/theorems/2c6e61ee-1457-4c17-9f59-6ef05a3c473c
-- title:
--   P2 M Ground Theory Variant  N1 rel Index sup of le normalizer 7514b13ff881: P2 M Ground Theory Variant  N1 rel Index sup of le normalizer 7514b13ff881
-- statement:
--   The P2 M Ground Theory Variant  N1 rel Index sup of le normalizer 7514b13ff881 construction uses the P2 M Ground Theory Variant  N1 rel Index sup of le normalizer 7514b13ff881 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/RelIndexSup.lean#L7-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/RelIndexSup.lean#L7-L44

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open Subgroup

theorem P2M_GroundTheory_Variant__N1_relIndex_sup_of_le_normalizer_7514b13ff881 {G : Type*} [Group G] {H N : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) : H.relIndex (H ⊔ N) = H.relIndex N := by sorry

alias «GroundTheory».«Variant₂».«N1».«relIndex_sup_of_le_normalizer» := P2M_GroundTheory_Variant__N1_relIndex_sup_of_le_normalizer_7514b13ff881
