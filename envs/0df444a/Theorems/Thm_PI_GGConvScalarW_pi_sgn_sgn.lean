-- Prove2me | Theorems.Thm_PI_GGConvScalarW_pi_sgn_sgn
-- name    : PI.GGConvScalarW.pi_sgn_sgn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:00.514106+00:00
-- url     : https://prove2.me/theorems/e1c01be7-84dc-4559-839c-ffb4e626353e
-- title:
--   GGConv Scalar W: pi sgn sgn
-- statement:
--   The GGConv Scalar W construction uses the pi sgn sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/IntertwinerRankLeOne.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/IntertwinerRankLeOne.lean#L23-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_CardUNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_AveragingOperatorIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_IntertwinerRankLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem PI.GGConvScalarW.pi_sgn_sgn (π : Representation ℂ (GL (Fin k) F) V) (v : V) : π (sgn k) (π (sgn k) v) = v := by sorry
