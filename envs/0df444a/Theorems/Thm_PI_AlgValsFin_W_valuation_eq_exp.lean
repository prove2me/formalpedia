-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_valuation_eq_exp
-- name    : PI.AlgValsFin.W.valuation_eq_exp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:13.26221+00:00
-- url     : https://prove2.me/theorems/ea34aa73-0d2d-4fc3-bf7e-0749503e8b85
-- title:
--   W: valuation eq exp
-- statement:
--   The W construction uses the valuation eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/FinprodNormEmbedding.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/FinprodNormEmbedding.lean#L11-L14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FinprodNormEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.valuation_eq_exp (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    v.valuation L (k : L) = WithZero.exp (-ordF v k) := by sorry
