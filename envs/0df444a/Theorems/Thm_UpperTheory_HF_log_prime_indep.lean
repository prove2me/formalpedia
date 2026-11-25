-- Prove2me | Theorems.Thm_UpperTheory_HF_log_prime_indep
-- name    : UpperTheory.HF.log_prime_indep
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:46.541087+00:00
-- url     : https://prove2.me/theorems/214c775e-e856-45f2-9501-c5b4fbbbe3eb
-- title:
--   HF: log prime indep
-- statement:
--   The HF construction uses the log prime indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/LogPrimeIndep.lean#L48-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/LogPrimeIndep.lean#L48-L79

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_LogPrimeIndep
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

theorem UpperTheory.HF.log_prime_indep :
    ∀ (S : Finset ℕ) (a b : ℕ → ℚ), (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (a l : ℝ) * Real.log l = ∑ l ∈ S, (b l : ℝ) * Real.log l → ∀ l ∈ S, a l = b l := by sorry
