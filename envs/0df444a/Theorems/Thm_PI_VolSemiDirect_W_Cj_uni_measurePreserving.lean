-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_uni_measurePreserving
-- name    : PI.VolSemiDirect.W.Cj.uni_measurePreserving
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:45:57.70974+00:00
-- url     : https://prove2.me/theorems/eadf8484-11ea-5386-ad6d-68ecece7d9ab
-- title:
--   Cj: uni measure Preserving
-- statement:
--   The Cj construction uses the uni measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/UniHaar.lean#L52-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/UniHaar.lean#L52-L84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_UniHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open MeasureTheory

theorem PI.VolSemiDirect.W.Cj.uni_measurePreserving {A : Type} [CommRing A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableMul₂ A] (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] :
    ∀ (k : ℕ) (U : Matrix (Fin k) (Fin k) A), (IsLowUni U ∨ IsLowUni U.transpose) →
      MeasurePreserving U.mulVec (Measure.pi fun _ : Fin k => ν)
        (Measure.pi fun _ : Fin k => ν) := by sorry
