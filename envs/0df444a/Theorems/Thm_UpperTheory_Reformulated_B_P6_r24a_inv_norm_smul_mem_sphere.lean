-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r24a_inv_norm_smul_mem_sphere
-- name    : UpperTheory.Reformulated.B.P6.r24a.inv_norm_smul_mem_sphere
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:24.44869+00:00
-- url     : https://prove2.me/theorems/f8f575d0-4318-5262-9468-5e3c96669d25
-- title:
--   r24a: inv norm smul mem sphere
-- statement:
--   The r24a construction uses the inv norm smul mem sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/InvNormSmulMemSphere.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/InvNormSmulMemSphere.lean#L11-L14

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_InvNormSmulMemSphere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r24a

theorem UpperTheory.Reformulated.B.P6.r24a.inv_norm_smul_mem_sphere {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by sorry
