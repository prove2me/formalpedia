-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_ModuliIntegralCharts_single_mem
-- name    : UpperTheory.Reformulated.B.ModuliIntegralCharts.single_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:19:31.17149+00:00
-- url     : https://prove2.me/theorems/2c5b3244-ac13-5fa8-919b-b498fe5bd46f
-- title:
--   Moduli Integral Charts: single mem
-- statement:
--   The Moduli Integral Charts construction uses the single mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ModuliIntegralCharts.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ModuliIntegralCharts.lean#L36-L42

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ModuliIntegralCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField

theorem UpperTheory.Reformulated.B.ModuliIntegralCharts.single_mem :
    ∀ (I : Formalism.MainNotions.S.AutInst) (i : Fin I.n), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ Pi.single i (↑N : I.E) ∈ I.L := by sorry
