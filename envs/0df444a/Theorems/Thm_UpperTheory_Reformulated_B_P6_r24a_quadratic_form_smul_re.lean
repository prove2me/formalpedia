-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r24a_quadratic_form_smul_re
-- name    : UpperTheory.Reformulated.B.P6.r24a.quadratic_form_smul_re
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:41.601638+00:00
-- url     : https://prove2.me/theorems/14c755f3-584b-4502-8a0b-e00cf02f2715
-- title:
--   r24a: quadratic form smul re
-- statement:
--   The r24a construction uses the quadratic form smul re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/InvNormSmulMemSphere.lean#L5-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/InvNormSmulMemSphere.lean#L5-L9

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

theorem UpperTheory.Reformulated.B.P6.r24a.quadratic_form_smul_re {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ) (x : V) :
    (Q (c • x) (c • x)).re = c ^ 2 * (Q x x).re := by sorry
