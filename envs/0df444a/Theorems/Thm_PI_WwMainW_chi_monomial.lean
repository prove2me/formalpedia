-- Prove2me | Theorems.Thm_PI_WwMainW_chi_monomial
-- name    : PI.WwMainW.chi_monomial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:46:14.112105+00:00
-- url     : https://prove2.me/theorems/7bf06a08-351b-4b4b-a4d4-92245f6aa8e5
-- title:
--   Ww Main W: chi monomial
-- statement:
--   The Ww Main W construction uses the chi monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/LfunEqOfSubset.lean#L80-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LFunctionMinors/LfunEqOfSubset.lean#L80-L92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_LfunEqOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open PI PI.WwMainW
open PI.WwMain PI.WwMain.KM

theorem PI.WwMainW.chi_monomial {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (z : Lt × Fin N0 × Fin N1 → ℂ_[l])
    (μ : (XZ Lt N0 N1) →₀ ℕ) (n : ℤ) :
    chi l N0 N1 z (monomial μ n) =
      C ((n : ℂ_[l]) * (Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun w e => z w ^ e) *
        monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1 1 := by sorry
