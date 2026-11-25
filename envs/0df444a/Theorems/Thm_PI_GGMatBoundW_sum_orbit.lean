-- Prove2me | Theorems.Thm_PI_GGMatBoundW_sum_orbit
-- name    : PI.GGMatBoundW.sum_orbit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:09:15.7965+00:00
-- url     : https://prove2.me/theorems/edc01b92-ffbb-52b0-8ca0-8a90d897c193
-- title:
--   GGMat Bound W: sum orbit
-- statement:
--   The GGMat Bound W construction uses the sum orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/MatrixCoefficientEquation.lean#L30-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/MatrixCoefficientEquation.lean#L30-L49

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_MatrixCoefficientEquation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {G : Type} [Group G] {X : Type} [MulAction Gᵐᵒᵖ X]

theorem PI.GGMatBoundW.sum_orbit [Fintype G] (hfree : ∀ (x : Gᵐᵒᵖ) (j : X), x • j = j → x = 1) (d : X → X → G)
    (hd : ∀ i j, (∃ x : Gᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) (f : G → ℂ) (i j : X) :
    (∑ x : G, if MulOpposite.op x • j = i then f x else 0) =
      if ∃ x : Gᵐᵒᵖ, x • j = i then f (d i j) else 0 := by sorry
