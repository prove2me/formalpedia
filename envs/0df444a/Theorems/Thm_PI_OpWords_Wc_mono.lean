-- Prove2me | Theorems.Thm_PI_OpWords_Wc_mono
-- name    : PI.OpWords.Wc_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:58.965107+00:00
-- url     : https://prove2.me/theorems/73cf5787-6e6c-4e4c-8248-3398377f17cf
-- title:
--   Op Words: Wc mono
-- statement:
--   The Op Words construction uses the Wc mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PairingPowMemSymbolRange.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PairingPowMemSymbolRange.lean#L18-L22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PairingPowMemSymbolRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable (K : Type) [Field K] [CharZero K] (k d : ℕ)

theorem PI.OpWords.Wc_mono {c c' : ℕ} (h : c ≤ c') : Wc K k d c ≤ Wc K k d c' := by sorry
