-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TM_midF_mX
-- name    : PI.PolynomialProperness.TM.midF_mX
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:17:27.739505+00:00
-- url     : https://prove2.me/theorems/03c4499b-9031-4b65-be99-44fcf06f2bca
-- title:
--   TM: mid F m X
-- statement:
--   The TM construction uses the mid F m X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L232-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L232-L239

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TM

theorem PI.PolynomialProperness.TM.midF_mX (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    midF k r (mX k r vX *ᵥ x) (mX k r vX *ᵥ y) = midF k r x y := by sorry
