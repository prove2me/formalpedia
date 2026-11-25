-- Prove2me | Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_frobG_of_coprime
-- name    : UpperTheory.HF.Formalism.HC.HostRaw.frobG_of_coprime
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:59.52344+00:00
-- url     : https://prove2.me/theorems/50922a66-4bce-4f1c-a286-aa0833f2db63
-- title:
--   Host Raw: frob G of coprime
-- statement:
--   The Host Raw construction uses the frob G of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/SizeDefs.lean#L40-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/SizeDefs.lean#L40-L40

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

theorem UpperTheory.HF.Formalism.HC.HostRaw.frobG_of_coprime {p : ℕ} (h : Nat.Coprime p H.condN) : H.frobG p = H.art (ZMod.unitOfCoprime p h) := by sorry
