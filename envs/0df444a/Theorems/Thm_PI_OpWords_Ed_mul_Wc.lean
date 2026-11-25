-- Prove2me | Theorems.Thm_PI_OpWords_Ed_mul_Wc
-- name    : PI.OpWords.Ed_mul_Wc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:28.24965+00:00
-- url     : https://prove2.me/theorems/d69a3588-172b-5a0b-a523-a9683c69680a
-- title:
--   Op Words: Ed mul Wc
-- statement:
--   The Op Words construction uses the Ed mul Wc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PairingPowMemSymbolRange.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PairingPowMemSymbolRange.lean#L24-L38

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

theorem PI.OpWords.Ed_mul_Wc (c : ℕ) (a b : Fin k) {B : Module.End K ↥(homogeneousSubmodule (Fin k) K d)}
    (hB : B ∈ Wc K k d c) : Formalism.MainNotions.TestSideCounting.Ed K k d a b * B ∈ Wc K k d (c + 1) := by sorry
