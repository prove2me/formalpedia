-- Prove2me | Theorems.Thm_QnRdSkewW_exp_mul_fix
-- name    : QnRdSkewW.exp_mul_fix
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:05:09.597127+00:00
-- url     : https://prove2.me/theorems/aa5aff7b-51a3-5310-afb7-241fd2d51c46
-- title:
--   Qn Rd Skew W: exp mul fix
-- statement:
--   The Qn Rd Skew W construction uses the exp mul fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/SkewReductionGroup.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/SkewReductionGroup.lean#L15-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_SkewReductionGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem QnRdSkewW.exp_mul_fix {n : ℕ} (X E : Matrix (Fin n) (Fin n) ℂ) (hXE : X * E = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * E = E := by sorry
