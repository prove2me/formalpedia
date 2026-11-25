-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_eN_H
-- name    : PI.PolynomialProperness.CoreW.eN_H
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:54.129623+00:00
-- url     : https://prove2.me/theorems/d1474330-84cc-4d0c-9a51-2e54252711a2
-- title:
--   Core W: e N H
-- statement:
--   The Core W construction uses the e N H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L63-L65

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
variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

theorem PI.PolynomialProperness.CoreW.eN_H (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) : eN (H *ᵥ v) = eN v := by sorry
