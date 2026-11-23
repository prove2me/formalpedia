-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Rd1_sum_comp_surj
-- name    : UpperTheory.Reformulated.B.Rd1.sum_comp_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:37.076803+00:00
-- url     : https://prove2.me/theorems/6a7b85ed-84ae-488e-9446-2c80ea26607b
-- title:
--   Rd1: sum comp surj
-- statement:
--   The Rd1 construction uses the sum comp surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SumCompSurj.lean#L3-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SumCompSurj.lean#L3-L22

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumCompSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Rd1.sum_comp_surj :
    ∀ {A B : Type} [inst : AddCommGroup A] [inst_1 : AddCommGroup B]
    [inst_2 : Fintype A] [inst_3 : Fintype B] (π : A →+ B),
    Function.Surjective (⇑π : A → B) →
      ∀ (G : B → ℂ), (↑(Fintype.card B) : ℂ) * ∑ a : A, G ((π : A → B) a) = (↑(Fintype.card A) : ℂ) * ∑ b : B, G b := by sorry
