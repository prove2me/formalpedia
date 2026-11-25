-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_exists_pow_close
-- name    : PI.AlgValsFin.W.exists_pow_close
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:54.166592+00:00
-- url     : https://prove2.me/theorems/d40bc439-75d4-5aba-b0a5-e863bca0185d
-- title:
--   W: exists pow close
-- statement:
--   The W construction uses the exists pow close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L50-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L50-L149

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem PI.AlgValsFin.W.exists_pow_close (n : ℕ) : ∃ N : ℕ, 0 < N ∧ ∀ x : v.adicCompletion L, Valued.v x = 1 →
    Valued.v (x ^ N - 1) ≤ exp (-(n : ℤ)) := by sorry
