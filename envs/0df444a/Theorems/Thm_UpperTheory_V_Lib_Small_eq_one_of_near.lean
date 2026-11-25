-- Prove2me | Theorems.Thm_UpperTheory_V_Lib_Small_eq_one_of_near
-- name    : UpperTheory.V.Lib.Small.eq_one_of_near
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:31.769816+00:00
-- url     : https://prove2.me/theorems/306f51f2-243d-478c-83cc-6577eb9728ee
-- title:
--   Small: eq one of near
-- statement:
--   The Small construction uses the eq one of near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/IntegralityNearIdentity/EqOneOfNear.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/IntegralityNearIdentity/EqOneOfNear.lean#L13-L15

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraAlt
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqOneOfNear
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraBis
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MirabolicColumnBlock
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitelyGeneratedModPow
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_IntegralityNearIdentity_EqOneOfNear
import Theorems.Thm_UpperTheory_Reformulated_B_S7_eq_one_of_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.V UpperTheory.V.Lib UpperTheory.V.Lib.Small

theorem UpperTheory.V.Lib.Small.eq_one_of_near {l : ℕ} [Fact l.Prime] {u : PadicAlgCl l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1)
    (h : ‖u - 1‖ < 1) : u = 1 := by sorry
