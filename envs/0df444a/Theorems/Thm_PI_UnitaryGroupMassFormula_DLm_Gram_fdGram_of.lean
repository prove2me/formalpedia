-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DLm_Gram_fdGram_of
-- name    : PI.UnitaryGroupMassFormula.DLm.Gram.fdGram_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:57:25.353958+00:00
-- url     : https://prove2.me/theorems/04d4455d-274a-511a-ad09-2e56da8c5410
-- title:
--   Gram: fd Gram of
-- statement:
--   The Gram construction uses the fd Gram of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFdGramCut.lean#L119-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFdGramCut.lean#L119-L171

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFdGramCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm PI.UnitaryGroupMassFormula.DLm.Gram

theorem PI.UnitaryGroupMassFormula.DLm.Gram.fdGram_of (hS : GramSlice) (hR : SmoothRep) (hE : FibEquivU) (hN : FiberIntegralUnipotentInvariant) : FdGram := by sorry
