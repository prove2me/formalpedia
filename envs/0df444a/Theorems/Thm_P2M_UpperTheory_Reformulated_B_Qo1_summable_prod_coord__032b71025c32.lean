-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qo1_summable_prod_coord__032b71025c32
-- name    : P2M_UpperTheory_Reformulated_B_Qo1_summable_prod_coord__032b71025c32
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:47.079136+00:00
-- url     : https://prove2.me/theorems/cd255415-8a53-5c07-b8b9-9635bb4f8382
-- title:
--   P2 M Upper Theory Reformulated B Qo1 summable prod coord  032b71025c32: P2 M Upper Theory Reformulated B Qo1 summable prod coord  032b71025c32
-- statement:
--   The P2 M Upper Theory Reformulated B Qo1 summable prod coord  032b71025c32 construction uses the P2 M Upper Theory Reformulated B Qo1 summable prod coord  032b71025c32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SummableProdCoord.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SummableProdCoord.lean#L26-L31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableProdCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qo1_summable_prod_coord__032b71025c32.{u_2, u_3} :
    ∀ {ι : Type u_2} [inst : Fintype ι] [DecidableEq ι] {α : Type u_3} {g : α → ℝ},
    (∀ (x : α), (0 : ℝ) ≤ g x) → Summable g → Summable fun (ξ : ι → α) ↦ ∏ i : ι, g (ξ i) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qo1».«summable_prod_coord».«» := P2M_UpperTheory_Reformulated_B_Qo1_summable_prod_coord__032b71025c32
