-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TM_mX_esI
-- name    : PI.PolynomialProperness.TM.mX_esI
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:37:11.905869+00:00
-- url     : https://prove2.me/theorems/40f6a5ab-e3b6-42fc-a68b-87079ff46b4b
-- title:
--   TM: m X es I
-- statement:
--   The TM construction uses the m X es I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L160-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L160-L172

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

theorem PI.PolynomialProperness.TM.mX_esI (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    mX k r vX (esI k r a) j =
      if h : r + k < j.val then (vXᴴ)⁻¹ a ⟨2 * r + k - j.val, by omega⟩ else 0 := by sorry
