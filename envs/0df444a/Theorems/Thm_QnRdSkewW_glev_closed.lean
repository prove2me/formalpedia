-- Prove2me | Theorems.Thm_QnRdSkewW_glev_closed
-- name    : QnRdSkewW.glev_closed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:01:44.204458+00:00
-- url     : https://prove2.me/theorems/b22e51c4-83cc-42f1-b5c8-42543c231bf9
-- title:
--   Qn Rd Skew W: glev closed
-- statement:
--   The Qn Rd Skew W construction uses the glev closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/SkewReductionGroup.lean#L83-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SkewAnalyticGroup/SkewReductionGroup.lean#L83-L95

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

theorem QnRdSkewW.glev_closed (k r : ℕ) (i : Fin (r + 1)) : IsClosed (Glev k r i) := by sorry
