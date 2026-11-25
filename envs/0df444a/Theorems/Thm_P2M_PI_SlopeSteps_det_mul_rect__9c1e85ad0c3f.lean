-- Prove2me | Theorems.Thm_P2M_PI_SlopeSteps_det_mul_rect__9c1e85ad0c3f
-- name    : P2M_PI_SlopeSteps_det_mul_rect__9c1e85ad0c3f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:15:40.577735+00:00
-- url     : https://prove2.me/theorems/d5cbd550-2dff-42e5-a0cd-ed98810fb643
-- title:
--   P2 M PI Slope Steps det mul rect  9c1e85ad0c3f: P2 M PI Slope Steps det mul rect  9c1e85ad0c3f
-- statement:
--   The P2 M PI Slope Steps det mul rect  9c1e85ad0c3f construction uses the P2 M PI Slope Steps det mul rect  9c1e85ad0c3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/NablaGram.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StandardSlopeBound/NablaGram.lean#L11-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV Matrix

theorem P2M_PI_SlopeSteps_det_mul_rect__9c1e85ad0c3f {R : Type*} [CommRing R] {k : ℕ} {n : Type*} [Fintype n]
    (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) :
    (A * B).det = ∑ f : Fin k → n, (∏ i, B (f i) i) * (A.submatrix id f).det := by sorry

alias «PI».«SlopeSteps».«det_mul_rect'» := P2M_PI_SlopeSteps_det_mul_rect__9c1e85ad0c3f
