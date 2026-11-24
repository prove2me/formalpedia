-- Prove2me | Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_mem_unitsOne
-- name    : UpperTheory.HF.Formalism.HC.HostRaw.mem_unitsOne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:27:01.513803+00:00
-- url     : https://prove2.me/theorems/edfd1b17-a81e-49c1-a817-a9137e8ba43e
-- title:
--   Host Raw: mem units One
-- statement:
--   The Host Raw construction uses the mem units One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffDefs.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffDefs.lean#L46-L49

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

theorem UpperTheory.HF.Formalism.HC.HostRaw.mem_unitsOne {f : ℕ} (hf : f ∣ H.condN) (u : (ZMod H.condN)ˣ) :
    u ∈ H.unitsOne f ↔ (u : ZMod H.condN).val ≡ 1 [MOD f] := by sorry
