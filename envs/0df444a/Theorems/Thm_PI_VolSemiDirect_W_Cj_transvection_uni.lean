-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_transvection_uni
-- name    : PI.VolSemiDirect.W.Cj.transvection_uni
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:48.25325+00:00
-- url     : https://prove2.me/theorems/bca2b2be-b3be-5906-80b9-5db5baae4867
-- title:
--   Cj: transvection uni
-- statement:
--   The Cj construction uses the transvection uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/UniHaar.lean#L95-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/UniHaar.lean#L95-L114

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

theorem PI.VolSemiDirect.W.Cj.transvection_uni {A : Type} [CommRing A] {k : ℕ} (i j : Fin k) (hij : i ≠ j) (c : A) :
    IsLowUni (Matrix.transvection i j c) ∨ IsLowUni (Matrix.transvection i j c).transpose := by sorry
