-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TM_mX_mulVec_esI
-- name    : PI.PolynomialProperness.TM.mX_mulVec_esI
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:38:14.303389+00:00
-- url     : https://prove2.me/theorems/6c498919-3d4b-4fab-8fe7-3cbd59aea497
-- title:
--   TM: m X mul Vec es I
-- statement:
--   The TM construction uses the m X mul Vec es I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L193-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L193-L215

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

theorem PI.PolynomialProperness.TM.mX_mulVec_esI (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (mX k r vX *ᵥ x) (esI k r a) = ((vXᴴ)⁻¹ *ᵥ qX k r x) a := by sorry
