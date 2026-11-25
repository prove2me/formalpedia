-- Prove2me | Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_sum_right
-- name    : PI.UnitaryDimensionFormula.FrameAlg.h_sum_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:52.399854+00:00
-- url     : https://prove2.me/theorems/d57c82b5-7ff0-5eed-ba78-9c2609d982e4
-- title:
--   Frame Alg: h sum right
-- statement:
--   The Frame Alg construction uses the h sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L26-L31

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

theorem PI.UnitaryDimensionFormula.FrameAlg.h_sum_right {ι : Type} (s : Finset ι) (x : n → A) (v : ι → n → A) :
    Formalism.UG.hform σ J x (∑ l ∈ s, v l) = ∑ l ∈ s, Formalism.UG.hform σ J x (v l) := by sorry
