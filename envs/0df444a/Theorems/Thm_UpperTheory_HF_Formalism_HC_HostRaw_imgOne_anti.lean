-- Prove2me | Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_imgOne_anti
-- name    : UpperTheory.HF.Formalism.HC.HostRaw.imgOne_anti
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:26:49.028066+00:00
-- url     : https://prove2.me/theorems/ea84f379-4284-4d71-8cfd-b1deecafc7a6
-- title:
--   Host Raw: img One anti
-- statement:
--   The Host Raw construction uses the img One anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffDefs.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffDefs.lean#L66-L68

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

theorem UpperTheory.HF.Formalism.HC.HostRaw.imgOne_anti {f g : ℕ} (hfg : f ∣ g) (hg : g ∣ H.condN) : H.imgOne g ≤ H.imgOne f := by sorry
