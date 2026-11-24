-- Prove2me | Theorems.Thm_QmCapCommW_glev_mul
-- name    : QmCapCommW.glev_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:52:48.600329+00:00
-- url     : https://prove2.me/theorems/524ee788-a597-4a40-ad69-39c5168190a2
-- title:
--   Qm Cap Comm W: glev mul
-- statement:
--   The Qm Cap Comm W construction uses the glev mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/CapelliOperatorCongruence.lean#L70-L81

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

theorem QmCapCommW.glev_mul {k r : ℕ} {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by sorry
