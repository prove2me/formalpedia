-- Prove2me | Theorems.Thm_P2M_RH_Bl_ProductIdentities_goal1_10f3307be02c86e1
-- name    : P2M_RH_Bl_ProductIdentities_goal1_10f3307be02c86e1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:11:20.246687+00:00
-- url     : https://prove2.me/theorems/6b755fac-1404-422a-bb72-71b2620e00d3
-- title:
--   P2 M RH Bl Product Identities goal1 10f3307be02c86e1: P2 M RH Bl Product Identities goal1 10f3307be02c86e1
-- statement:
--   The P2 M RH Bl Product Identities goal1 10f3307be02c86e1 construction uses the P2 M RH Bl Product Identities goal1 10f3307be02c86e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/ProductIdentities.lean#L22-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/ProductIdentities.lean#L22-L49

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_ProductIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.ProductIdentities

theorem P2M_RH_Bl_ProductIdentities_goal1_10f3307be02c86e1 :
  ∀ {n : Type} [inst : Fintype.{0} n] [inst_1 : DecidableEq.{1} n] (A : Real → Matrix.{0, 0, 0} n n Complex)
  (A' : Matrix.{0, 0, 0} n n Complex),
  Eq.{1} (A 0) 1 →
    (∀ (i j : n), HasDerivAt.{0, 0} (fun (t : Real) ↦ A t i j) (A' i j) 0) →
      HasDerivAt.{0, 0} (fun (t : Real) ↦ Matrix.det.{0, 0} (A t)) (Matrix.trace.{0, 0} A') 0 := by sorry

alias «Bl».«ProductIdentities».«goal1» := P2M_RH_Bl_ProductIdentities_goal1_10f3307be02c86e1
