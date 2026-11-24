-- Prove2me | Theorems.Thm_UpperTheory_HF_log_rd_sum
-- name    : UpperTheory.HF.log_rd_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:43:25.194917+00:00
-- url     : https://prove2.me/theorems/0637b7cd-f66f-43c7-9a1c-158c8cded553
-- title:
--   HF: log rd sum
-- statement:
--   The HF construction uses the log rd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/LogRdSum.lean#L8-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/LogRdSum.lean#L8-L34

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogRdSum
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

theorem UpperTheory.HF.log_rd_sum :
    ∀ {φ : Frame} (H : HostAx φ), Real.log H.rd = ∑ l ∈ H.ram, H.vdH l * Real.log l ∧ Real.log H.rd = ∑ l ∈ H.condN.primeFactors, H.vdH l * Real.log l ∧ H.ram ⊆ H.condN.primeFactors ∧ 0 < H.rd := by sorry
