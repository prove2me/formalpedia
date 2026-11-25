-- Prove2me | Theorems.Thm_UpperTheory_Ram_two_fm_le_rdE
-- name    : UpperTheory.Ram.two_fm_le_rdE
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:25:17.081663+00:00
-- url     : https://prove2.me/theorems/e45dfac1-e51a-4831-80ba-3e869e2ac2bb
-- title:
--   Ram: two fm le rd E
-- statement:
--   The Ram construction uses the two fm le rd E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/TwoFmLeRdE.lean#L7-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/TwoFmLeRdE.lean#L7-L49

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_LogQdLeRd
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_TwoFmLeRdE
import Theorems.Thm_Formalism_FrobeniusOrbits_DiscrB_rdE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions

theorem UpperTheory.Ram.two_fm_le_rdE :
    ∀ (R : Ranks) (H : Host R), 2 * (R.f : ℝ) * R.m ≤ H.rdE ∧ 4 * (R.t : ℝ) * R.r + 1 ≤ H.rdE := by sorry
