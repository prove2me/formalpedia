-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793
-- name    : P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:36.244776+00:00
-- url     : https://prove2.me/theorems/bff450d5-c3f2-46df-a10c-a3ed3aeb47c4
-- title:
--   P2 M Upper Theory Reformulated B Qi25 sum  8f7927b3f793: P2 M Upper Theory Reformulated B Qi25 sum  8f7927b3f793
-- statement:
--   The P2 M Upper Theory Reformulated B Qi25 sum  8f7927b3f793 construction uses the P2 M Upper Theory Reformulated B Qi25 sum  8f7927b3f793 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EvalDet.lean#L28-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EvalDet.lean#L28-L47

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793.{u_1} :
    ∀ {N : ℕ} {ι : Type u_1} (s : Finset ι) {F : ι → UpperTheory.Reformulated.B.Qi25.UG N → ℂ},
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi25.IsPD (F i)) → UpperTheory.Reformulated.B.Qi25.IsPD fun (g : UpperTheory.Reformulated.B.Qi25.UG N) ↦ ∑ i ∈ s, F i g := by sorry

alias «UpperTheory».«Reformulated».«B».«Qi25».«sum» := P2M_UpperTheory_Reformulated_B_Qi25_sum__8f7927b3f793
