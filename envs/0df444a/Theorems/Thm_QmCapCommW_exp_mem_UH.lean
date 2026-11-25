-- Prove2me | Theorems.Thm_QmCapCommW_exp_mem_UH
-- name    : QmCapCommW.exp_mem_UH
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:13.989967+00:00
-- url     : https://prove2.me/theorems/ee407132-858d-5aa9-995b-157dc834da8c
-- title:
--   Qm Cap Comm W: exp mem UH
-- statement:
--   The Qm Cap Comm W construction uses the exp mem UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L52-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L52-L68

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

theorem QmCapCommW.exp_mem_UH {n : ℕ} (H Y : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ UH H := by sorry
