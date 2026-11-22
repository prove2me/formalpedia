-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qj14_kap_mem
-- name    : UpperTheory.Reformulated.B.Qj14.kap_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:39.237135+00:00
-- url     : https://prove2.me/theorems/ab91edb3-7d4e-4096-bf8d-27745ee1f8ee
-- title:
--   Qj14: kap mem
-- statement:
--   The Qj14 construction uses the kap mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CayleyForm.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CayleyForm.lean#L53-L58

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qj14.kap_mem :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qj14.Mat k r},
      UpperTheory.Reformulated.B.Qj14.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qj14.kap Y ∈ UpperTheory.Reformulated.B.Qj14.GV k r := by sorry
