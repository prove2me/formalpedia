-- Prove2me | Theorems.Thm_UpperTheory_KR_log_qd_le_rd
-- name    : UpperTheory.KR.log_qd_le_rd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:12.32447+00:00
-- url     : https://prove2.me/theorems/4bb6c869-98b1-458d-95f7-6deb60179b4d
-- title:
--   KR: log qd le rd
-- statement:
--   The KR construction uses the log qd le rd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/LogQdLeRd.lean#L11-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/LogQdLeRd.lean#L11-L46

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RadBounds2
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_RamEq
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTwo
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_LogQdLeRd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.HF
open NumberField Formalism.HC

theorem UpperTheory.KR.log_qd_le_rd :
    ∀ {φ : Frame} (H : HostAx φ), H.toHostRaw.PsQ → H.q ∈ H.ram ∧ Real.log H.q + Real.log H.d ≤ 2 * Real.log H.rd ∧ Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd ∧ 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ H.rd := by sorry
