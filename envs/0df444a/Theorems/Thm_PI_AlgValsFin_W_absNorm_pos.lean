-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_absNorm_pos
-- name    : PI.AlgValsFin.W.absNorm_pos
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:26.509499+00:00
-- url     : https://prove2.me/theorems/06663329-5e63-54ca-8af0-4987895ee7ae
-- title:
--   W: abs Norm pos
-- statement:
--   The W construction uses the abs Norm pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/FactorOne.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/FactorOne.lean#L11-L15

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FactorOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.absNorm_pos (v : HeightOneSpectrum (𝓞 L)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by sorry
