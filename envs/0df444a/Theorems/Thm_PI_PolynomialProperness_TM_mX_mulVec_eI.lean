-- Prove2me | Theorems.Thm_PI_PolynomialProperness_TM_mX_mulVec_eI
-- name    : PI.PolynomialProperness.TM.mX_mulVec_eI
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:38:40.983927+00:00
-- url     : https://prove2.me/theorems/e7b0eff5-256a-48e4-aeb9-d2b923005e33
-- title:
--   TM: m X mul Vec e I
-- statement:
--   The TM construction uses the m X mul Vec e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L179-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/MXMulVecMid.lean#L179-L191

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

theorem PI.PolynomialProperness.TM.mX_mulVec_eI (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (mX k r vX *ᵥ x) (eI k r a) = (vX *ᵥ pX k r x) a := by sorry
