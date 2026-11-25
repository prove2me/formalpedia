-- Prove2me | Theorems.Thm_UpperTheory_HF_cond_rd
-- name    : UpperTheory.HF.cond_rd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:56.111604+00:00
-- url     : https://prove2.me/theorems/a2ff0c8a-6c16-5fa4-bac1-b65dfe39b259
-- title:
--   HF: cond rd
-- statement:
--   The HF construction uses the cond rd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/CondRd.lean#L58-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/CondRd.lean#L58-L106

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdLe
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MemRam
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdFormula
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LayerBot
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondESpec
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CardImgOneDvd
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_CondRd
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

theorem UpperTheory.HF.cond_rd :
    ∀ {φ : Frame} (H : HostAx φ), H.rd ≤ H.condE ∧ Real.log H.rd ≤ Real.log H.condE ∧ Real.log H.condE ≤ Real.log H.condN ∧ (H.condE : ℝ) ≤ H.rd ^ 2 ∧ 4 * φ.ord ≤ H.condE.totient ∧ 4 * φ.ord ∣ H.condE.totient ∧ 4 * φ.ord ≤ H.condE := by sorry
