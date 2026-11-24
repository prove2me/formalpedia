-- Prove2me | Theorems.Thm_PI_PolynomialProperness_CB_det_norm_le
-- name    : PI.PolynomialProperness.CB.det_norm_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:39:05.420132+00:00
-- url     : https://prove2.me/theorems/9c2e6947-8eef-4a0e-bb84-c0af0b6e5f4b
-- title:
--   CB: det norm le
-- statement:
--   The CB construction uses the det norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/SecondOrderNormBound.lean#L26-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB

theorem PI.PolynomialProperness.CB.det_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) {c : ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ c) : ‖A.det‖ ≤ (Fintype.card ι).factorial * c ^ Fintype.card ι := by sorry
