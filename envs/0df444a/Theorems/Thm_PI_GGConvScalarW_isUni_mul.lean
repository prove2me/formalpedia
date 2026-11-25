-- Prove2me | Theorems.Thm_PI_GGConvScalarW_isUni_mul
-- name    : PI.GGConvScalarW.isUni_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:34.750648+00:00
-- url     : https://prove2.me/theorems/1849e5b5-9218-4e87-9acf-fd7f7fed0f21
-- title:
--   GGConv Scalar W: is Uni mul
-- statement:
--   The GGConv Scalar W construction uses the is Uni mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L83-L85

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}

theorem PI.GGConvScalarW.isUni_mul {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) : IsUni k (x * y) := by sorry
