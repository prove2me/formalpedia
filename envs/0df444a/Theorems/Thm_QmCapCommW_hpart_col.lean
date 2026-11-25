-- Prove2me | Theorems.Thm_QmCapCommW_hpart_col
-- name    : QmCapCommW.hpart_col
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:52:20.540069+00:00
-- url     : https://prove2.me/theorems/6f68aeb6-bbb7-4240-967f-d33fb4b62136
-- title:
--   Qm Cap Comm W: hpart col
-- statement:
--   The Qm Cap Comm W construction uses the hpart col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L157-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L157-L162

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

theorem QmCapCommW.hpart_col {k r : ℕ} {i : Fin (r + 1)} (a b : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcb : c ≠ posL k r i b) (hac : Hpk k r (posL k r i a) c = 0) (s : ℂ) (j : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) + s • ((Hpk k r)⁻¹ *
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r)) j c = 0 := by sorry
