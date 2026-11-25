-- Prove2me | Theorems.Thm_QmCapCommW_skew_plus
-- name    : QmCapCommW.skew_plus
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:48.830783+00:00
-- url     : https://prove2.me/theorems/ff5aad36-c76a-48bd-b2c9-ed5a6cc6e0ed
-- title:
--   Qm Cap Comm W: skew plus
-- statement:
--   The Qm Cap Comm W construction uses the skew plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L107-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L107-L117

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

theorem QmCapCommW.skew_plus {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hh : Hᴴ = H) (hHH : H * H = 1) :
    H * (Z + H * Zᴴ * H) - (Z + H * Zᴴ * H)ᴴ * H = 0 := by sorry
