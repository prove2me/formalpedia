-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_eN_sub
-- name    : PI.PolynomialProperness.CoreW.eN_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:20:01.652828+00:00
-- url     : https://prove2.me/theorems/1b3f791e-1d80-4c04-90d3-fb192097d9f2
-- title:
--   Core W: e N sub
-- statement:
--   The Core W construction uses the e N sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L18-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_HermProjRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CoreW

theorem PI.PolynomialProperness.CoreW.eN_sub {n : ℕ} (x y : Fin n → ℂ) : eN (x - y) ≤ eN x + eN y := by sorry
