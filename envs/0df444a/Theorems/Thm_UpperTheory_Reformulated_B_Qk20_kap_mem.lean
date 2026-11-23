-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qk20_kap_mem
-- name    : UpperTheory.Reformulated.B.Qk20.kap_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:17.045343+00:00
-- url     : https://prove2.me/theorems/a1289594-5769-4d99-b823-a21073fed134
-- title:
--   Qk20: kap mem
-- statement:
--   The Qk20 construction uses the kap mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CayleyTransformPreservesForm.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CayleyTransformPreservesForm.lean#L50-L55

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qk20.kap_mem :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qk20.Mat k r},
      UpperTheory.Reformulated.B.Qk20.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qk20.kap Y ∈ UpperTheory.Reformulated.B.Qk20.GV k r := by sorry
