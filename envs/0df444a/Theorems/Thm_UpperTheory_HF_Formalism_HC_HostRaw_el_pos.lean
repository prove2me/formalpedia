-- Prove2me | Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_el_pos
-- name    : UpperTheory.HF.Formalism.HC.HostRaw.el_pos
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:26:50.562958+00:00
-- url     : https://prove2.me/theorems/4947fee1-7c6d-4cf5-bb84-df0f2310bf5f
-- title:
--   Host Raw: el pos
-- statement:
--   The Host Raw construction uses the el pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffDefs.lean#L70-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffDefs.lean#L70-L70

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.HF UpperTheory.HF.Formalism UpperTheory.HF.Formalism.HC UpperTheory.HF.Formalism.HC.HostRaw
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)

theorem UpperTheory.HF.Formalism.HC.HostRaw.el_pos (l : ℕ) : 0 < H.el l := by sorry
