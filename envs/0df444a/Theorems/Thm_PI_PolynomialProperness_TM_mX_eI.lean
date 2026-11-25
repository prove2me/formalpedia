-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TM_mX_eI
-- name    : PI.PolynomialProperness.TM.mX_eI
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:58:34.728193+00:00
-- url     : https://prove2.me/theorems/a271f678-1df9-448b-8733-05cb3fa83fb0
-- title:
--   TM: m X e I
-- statement:
--   The TM construction uses the m X e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L154-L158

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

theorem PI.PolynomialProperness.TM.mX_eI (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    mX k r vX (eI k r a) j = if h : j.val < r then vX a ⟨j.val, h⟩ else 0 := by sorry
