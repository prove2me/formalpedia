-- Prove2me | Theorems.Thm_PI_BeConjNormW_coeff_one_subst
-- name    : PI.BeConjNormW.coeff_one_subst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:27.424268+00:00
-- url     : https://prove2.me/theorems/31415dbd-d66b-5cb2-bfbe-89ad61923f1a
-- title:
--   Be Conj Norm W: coeff one subst
-- statement:
--   The Be Conj Norm W construction uses the coeff one subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateNormBound/BeConjNormOfIntInv.lean#L15-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateNormBound/BeConjNormOfIntInv.lean#L15-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BeConjNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_BeConjNormOfIntInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeConjNormW
open PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeConjNormW.coeff_one_subst (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst a f : PowerSeries ℂ_[p]) = PowerSeries.coeff 1 f * PowerSeries.coeff 1 a := by sorry
