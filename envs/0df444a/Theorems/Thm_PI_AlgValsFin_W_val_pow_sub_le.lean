-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_val_pow_sub_le
-- name    : PI.AlgValsFin.W.val_pow_sub_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:00:21.993564+00:00
-- url     : https://prove2.me/theorems/e937451d-c2a8-4c93-a6ca-e795fd8db943
-- title:
--   W: val pow sub le
-- statement:
--   The W construction uses the val pow sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L14-L24

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

theorem PI.AlgValsFin.W.val_pow_sub_le {x b : v.adicCompletion L} (hx : Valued.v x ≤ 1) (hb : Valued.v b ≤ 1) (k : ℕ) :
    Valued.v (x ^ k - b ^ k) ≤ Valued.v (x - b) := by sorry
