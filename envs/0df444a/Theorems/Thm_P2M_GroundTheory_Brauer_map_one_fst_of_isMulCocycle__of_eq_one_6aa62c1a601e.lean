-- Prove2me | Theorems.Thm_P2M_GroundTheory_Brauer_map_one_fst_of_isMulCocycle__of_eq_one_6aa62c1a601e
-- name    : P2M_GroundTheory_Brauer_map_one_fst_of_isMulCocycle__of_eq_one_6aa62c1a601e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:44.947113+00:00
-- url     : https://prove2.me/theorems/ea9e49ea-7c3c-4d52-acba-1f91fa82af41
-- title:
--   P2 M Ground Theory Brauer map one fst of is Mul Cocycle  of eq one 6aa62c1a601e: P2 M Ground Theory Brauer map one fst of is Mul Cocycle  of eq one 6aa62c1a601e
-- statement:
--   The P2 M Ground Theory Brauer map one fst of is Mul Cocycle  of eq one 6aa62c1a601e construction uses the P2 M Ground Theory Brauer map one fst of is Mul Cocycle  of eq one 6aa62c1a601e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/MulDistribMulActionQuotientFixedPoints.lean#L72-L74

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

theorem P2M_GroundTheory_Brauer_map_one_fst_of_isMulCocycle__of_eq_one_6aa62c1a601e {f : G × G → M} (hf : IsMulCocycle₂ f)
    (h1 : f (1, 1) = 1) (g : G) : f (1, g) = 1 := by sorry

alias «GroundTheory».«Brauer».«map_one_fst_of_isMulCocycle₂_of_eq_one» := P2M_GroundTheory_Brauer_map_one_fst_of_isMulCocycle__of_eq_one_6aa62c1a601e
