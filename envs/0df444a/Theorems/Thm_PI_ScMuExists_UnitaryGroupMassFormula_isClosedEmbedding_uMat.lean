-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosedEmbedding_uMat
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.isClosedEmbedding_uMat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:02:45.450308+00:00
-- url     : https://prove2.me/theorems/2183e4a7-1cef-4e84-96b5-3f2e993952af
-- title:
--   Unitary Group Mass Formula: is Closed Embedding u Mat
-- statement:
--   The Unitary Group Mass Formula construction uses the is Closed Embedding u Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/Proper.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/Proper.lean#L16-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousHPart
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_Proper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped Pointwise
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula

theorem PI.ScMuExists.UnitaryGroupMassFormula.isClosedEmbedding_uMat {n : ℕ} (ε : Fin n → Bool) :
    Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) := by sorry
