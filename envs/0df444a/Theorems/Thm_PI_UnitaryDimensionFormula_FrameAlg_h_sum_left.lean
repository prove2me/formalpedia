-- Prove2me | Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_sum_left
-- name    : PI.UnitaryDimensionFormula.FrameAlg.h_sum_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:36.467072+00:00
-- url     : https://prove2.me/theorems/4a2b22b1-390e-44cc-ba29-c996b5b824f5
-- title:
--   Frame Alg: h sum left
-- statement:
--   The Frame Alg construction uses the h sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L45-L50

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

theorem PI.UnitaryDimensionFormula.FrameAlg.h_sum_left {ι : Type} (s : Finset ι) (v : ι → n → A) (y : n → A) :
    Formalism.UG.hform σ J (∑ l ∈ s, v l) y = ∑ l ∈ s, Formalism.UG.hform σ J (v l) y := by sorry
