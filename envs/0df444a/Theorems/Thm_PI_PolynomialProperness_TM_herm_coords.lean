-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TM_herm_coords
-- name    : PI.PolynomialProperness.TM.herm_coords
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:37:21.546268+00:00
-- url     : https://prove2.me/theorems/54b364ae-01e2-596e-9500-31c59554eb34
-- title:
--   TM: herm coords
-- statement:
--   The TM construction uses the herm coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L61-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L61-L127

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

theorem PI.PolynomialProperness.TM.herm_coords (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (qX k r y) ⬝ᵥ pX k r x + star (pX k r y) ⬝ᵥ qX k r x + midF k r x y := by sorry
