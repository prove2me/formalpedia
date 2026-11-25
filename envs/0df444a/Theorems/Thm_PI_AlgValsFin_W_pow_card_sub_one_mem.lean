-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_pow_card_sub_one_mem
-- name    : PI.AlgValsFin.W.pow_card_sub_one_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:23:02.3316+00:00
-- url     : https://prove2.me/theorems/f4cfe70e-43c3-595c-8572-e34bc46b6524
-- title:
--   W: pow card sub one mem
-- statement:
--   The W construction uses the pow card sub one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L26-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L26-L44

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

theorem PI.AlgValsFin.W.pow_card_sub_one_mem (n : ℕ) (b : 𝓞 L) (hb : b ∉ v.asIdeal) :
    b ^ Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ) - 1 ∈ v.asIdeal ^ n := by sorry
