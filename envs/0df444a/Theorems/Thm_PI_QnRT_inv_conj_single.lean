-- Prove2me | Theorems.Thm_PI_QnRT_inv_conj_single
-- name    : PI.QnRT.inv_conj_single
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:16.36678+00:00
-- url     : https://prove2.me/theorems/9f891626-4739-401e-92df-6a5d7e796007
-- title:
--   Qn RT: inv conj single
-- statement:
--   The Qn RT construction uses the inv conj single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusConjugationRule/SecondHermitianPartDiagonal.lean#L92-L95

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

theorem PI.QnRT.inv_conj_single (x : Fin (2 * r + k + 1)) :
    (Hpk k r)⁻¹ * (single x x (1 : ℂ))ᴴ * Hpk k r =
      single (WeylGroupFacts.tau k r x) (WeylGroupFacts.tau k r x) 1 := by sorry
