-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qp7_summable_absNorm_rpow_inv__1131da3fa2ce
-- name    : P2M_UpperTheory_Reformulated_B_Qp7_summable_absNorm_rpow_inv__1131da3fa2ce
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:52.308602+00:00
-- url     : https://prove2.me/theorems/fefd4c9c-e726-42bd-b85f-aa4dc1705750
-- title:
--   P2 M Upper Theory Reformulated B Qp7 summable abs Norm rpow inv  1131da3fa2ce: P2 M Upper Theory Reformulated B Qp7 summable abs Norm rpow inv  1131da3fa2ce
-- statement:
--   The P2 M Upper Theory Reformulated B Qp7 summable abs Norm rpow inv  1131da3fa2ce construction uses the P2 M Upper Theory Reformulated B Qp7 summable abs Norm rpow inv  1131da3fa2ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SummableAbsNormRpowInv.lean#L41-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SummableAbsNormRpowInv.lean#L41-L55

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Asymptotics NumberField

theorem P2M_UpperTheory_Reformulated_B_Qp7_summable_absNorm_rpow_inv__1131da3fa2ce.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {σ : ℝ},
    (1 : ℝ) < σ →
      Summable fun (I : Ideal (NumberField.RingOfIntegers K)) ↦
        ((↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) I) : ℝ) ^ σ)⁻¹ := by sorry

alias «UpperTheory».«Reformulated».«B».«Qp7».«summable_absNorm_rpow_inv».«» := P2M_UpperTheory_Reformulated_B_Qp7_summable_absNorm_rpow_inv__1131da3fa2ce
