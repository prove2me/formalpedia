-- Prove2me | Theorems.Thm_QmCapCommW_hpart2_lie
-- name    : QmCapCommW.hpart2_lie
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:05:48.506046+00:00
-- url     : https://prove2.me/theorems/b29b561e-95e0-5f2a-801d-77420f260f58
-- title:
--   Qm Cap Comm W: hpart2 lie
-- statement:
--   The Qm Cap Comm W construction uses the hpart2 lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L175-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L175-L184

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open QmCapCommW
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem QmCapCommW.hpart2_lie {k r : ℕ} (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by sorry
