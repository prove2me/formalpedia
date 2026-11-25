-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CoreW_herm_smul_right
-- name    : PI.PolynomialProperness.CoreW.herm_smul_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:36:11.573262+00:00
-- url     : https://prove2.me/theorems/bb6096e2-91a5-559b-acf2-e2844f8e8758
-- title:
--   Core W: herm smul right
-- statement:
--   The Core W construction uses the herm smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/HermProjRight.lean#L102-L104

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

theorem PI.PolynomialProperness.CoreW.herm_smul_right (hH : Hᴴ = H) (c : ℂ) (v w : Fin n → ℂ) :
    herm H v (c • w) = conj c * herm H v w := by sorry
