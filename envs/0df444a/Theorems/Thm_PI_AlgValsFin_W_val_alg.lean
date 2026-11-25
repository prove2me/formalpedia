-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_val_alg
-- name    : PI.AlgValsFin.W.val_alg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:23:11.703795+00:00
-- url     : https://prove2.me/theorems/1303c3b6-12cb-4d84-bcea-ae7559b666d3
-- title:
--   W: val alg
-- statement:
--   The W construction uses the val alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L11-L12

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

theorem PI.AlgValsFin.W.val_alg (y : L) : Valued.v (algebraMap L (v.adicCompletion L) y) = v.valuation L y := by sorry
