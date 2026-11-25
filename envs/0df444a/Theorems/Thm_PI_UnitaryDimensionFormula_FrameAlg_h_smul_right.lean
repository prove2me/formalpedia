-- Prove2me | Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_smul_right
-- name    : PI.UnitaryDimensionFormula.FrameAlg.h_smul_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:37:49.907871+00:00
-- url     : https://prove2.me/theorems/13d18bd7-8aa3-425f-9580-9f7f999e73c7
-- title:
--   Frame Alg: h smul right
-- statement:
--   The Frame Alg construction uses the h smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L14-L17

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open PI PI.UnitaryDimensionFormula PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)

theorem PI.UnitaryDimensionFormula.FrameAlg.h_smul_right (x y : n → A) (a : A) :
    Formalism.UG.hform σ J x (a • y) = a * Formalism.UG.hform σ J x y := by sorry
