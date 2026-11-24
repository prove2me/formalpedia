-- Prove2me | Theorems.Thm_PI_QnRT_hpk_inv
-- name    : PI.QnRT.hpk_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:05:59.666601+00:00
-- url     : https://prove2.me/theorems/641825c0-480d-41d3-bbca-db1cd76c9b27
-- title:
--   Qn RT: hpk inv
-- statement:
--   The Qn RT construction uses the hpk inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L50-L50

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}

theorem PI.QnRT.hpk_inv : (Hpk k r)⁻¹ = Hpk k r := by sorry
