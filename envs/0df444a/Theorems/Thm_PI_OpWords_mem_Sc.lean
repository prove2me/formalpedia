-- Prove2me | Theorems.Thm_PI_OpWords_mem_Sc
-- name    : PI.OpWords.mem_Sc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:35.42456+00:00
-- url     : https://prove2.me/theorems/aaa419fc-7bb7-4c9b-9198-4a973e05cf37
-- title:
--   Op Words: mem Sc
-- statement:
--   The Op Words construction uses the mem Sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PairingPowMemSymbolRange.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/PairingPowMemSymbolRange.lean#L15-L16

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

theorem PI.OpWords.mem_Sc (c : ℕ) (g : Pol K k) :
    g ∈ Sc K k d c ↔ tt K k ^ (d - c) * g ∈ (Wc K k d c).map (kappa K k d) := by sorry
