-- Prove2me | Theorems.Thm_P2M_GroundTheory_Brauer_map_one_snd_of_isMulCocycle__of_eq_one_f07df9f0d9d6
-- name    : P2M_GroundTheory_Brauer_map_one_snd_of_isMulCocycle__of_eq_one_f07df9f0d9d6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:42.011808+00:00
-- url     : https://prove2.me/theorems/16c7f858-4b6b-4724-b3fb-ce7199e90810
-- title:
--   P2 M Ground Theory Brauer map one snd of is Mul Cocycle  of eq one f07df9f0d9d6: P2 M Ground Theory Brauer map one snd of is Mul Cocycle  of eq one f07df9f0d9d6
-- statement:
--   The P2 M Ground Theory Brauer map one snd of is Mul Cocycle  of eq one f07df9f0d9d6 construction uses the P2 M Ground Theory Brauer map one snd of is Mul Cocycle  of eq one f07df9f0d9d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L76-L78

import Mathlib
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v u' v'
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
variable {G M}

theorem P2M_GroundTheory_Brauer_map_one_snd_of_isMulCocycle__of_eq_one_f07df9f0d9d6 {f : G × G → M} (hf : IsMulCocycle₂ f)
    (h1 : f (1, 1) = 1) (g : G) : f (g, 1) = 1 := by sorry

alias «GroundTheory».«Brauer».«map_one_snd_of_isMulCocycle₂_of_eq_one» := P2M_GroundTheory_Brauer_map_one_snd_of_isMulCocycle__of_eq_one_f07df9f0d9d6
