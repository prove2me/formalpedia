-- Prove2me | Theorems.Thm_UpperTheory_HF_layer_bot
-- name    : UpperTheory.HF.layer_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:28:13.249325+00:00
-- url     : https://prove2.me/theorems/168eaf0d-ddf6-43fd-9433-f9aa8140c320
-- title:
--   HF: layer bot
-- statement:
--   The HF construction uses the layer bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/LayerBot.lean#L38-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/LayerBot.lean#L38-L61

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondESpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CardImgOneDvd
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.layer_bot :
    ∀ {φ : Frame} (H : HostRaw φ) {l j : ℕ}, l.Prime → j ≤ H.condN.factorization l → (H.imgOne (ordCompl[l] H.condN * l ^ j) = ⊥ ↔ H.condE.factorization l ≤ j) ∧ (j ≤ H.condE.factorization l → Nat.card (H.imgOne (ordCompl[l] H.condN * l ^ j)) ∣ (l ^ H.condE.factorization l).totient / (l ^ j).totient) ∧ H.condE.factorization l ≤ H.condN.factorization l := by sorry
