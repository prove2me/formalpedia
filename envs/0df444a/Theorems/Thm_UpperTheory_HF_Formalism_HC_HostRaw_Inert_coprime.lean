-- Prove2me | Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_Inert_coprime
-- name    : UpperTheory.HF.Formalism.HC.HostRaw.Inert.coprime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:46.184346+00:00
-- url     : https://prove2.me/theorems/434b1e71-77e2-5635-874b-5c5ecfb7e3e4
-- title:
--   Inert: coprime
-- statement:
--   The Inert construction uses the coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/SizeDefs.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/SizeDefs.lean#L56-L57

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open UpperTheory UpperTheory.HF UpperTheory.HF.Formalism UpperTheory.HF.Formalism.HC
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC
open UpperTheory.HF.Formalism.HC.HostRaw
open _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)

theorem UpperTheory.HF.Formalism.HC.HostRaw.Inert.coprime {H : HostRaw φ} {p : ℕ} (h : H.Inert p) : Nat.Coprime p H.condN := by sorry
