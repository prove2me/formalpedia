-- Prove2me | Theorems.Thm_PI_UnitaryDimensionFormula_FrameAlg_h_smul_left
-- name    : PI.UnitaryDimensionFormula.FrameAlg.h_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:49:59.272416+00:00
-- url     : https://prove2.me/theorems/4f877d8f-56bc-411a-971e-87b4224dd7a1
-- title:
--   Frame Alg: h smul left
-- statement:
--   The Frame Alg construction uses the h smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean#L37-L40

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

theorem PI.UnitaryDimensionFormula.FrameAlg.h_smul_left (x y : n → A) (a : A) :
    Formalism.UG.hform σ J (a • x) y = σ a * Formalism.UG.hform σ J x y := by sorry
