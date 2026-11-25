-- Prove2me | Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_symm
-- name    : PI.UnitaryDimensionFormula.FrameAlg.h_symm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:39:11.187582+00:00
-- url     : https://prove2.me/theorems/f7aa7929-00a2-5fd7-bd06-8203b111e960
-- title:
--   Frame Alg: h symm
-- statement:
--   The Frame Alg construction uses the h symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L52-L62

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

theorem PI.UnitaryDimensionFormula.FrameAlg.h_symm (hJ : Formalism.UG.cT σ J = J) (hσ : ∀ a, σ (σ a) = a) (x y : n → A) :
    Formalism.UG.hform σ J y x = σ (Formalism.UG.hform σ J x y) := by sorry
