-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_step
-- name    : PI.VolSemiDirect.W.Cj.step
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:21.754196+00:00
-- url     : https://prove2.me/theorems/184d055b-da04-4442-937e-ca048c50483d
-- title:
--   Cj: step
-- statement:
--   The Cj construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L126-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L126-L278

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag
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
open Matrix
variable {A : Type} [CommRing A] {k : ℕ}

theorem PI.VolSemiDirect.W.Cj.step (hA : HasStableRangeOne A) (m : ℕ) (hm : m < k) (X : GL (Fin k) A)
    (hX : Red m (X : Matrix (Fin k) (Fin k) A)) :
    ∃ g ∈ Subgroup.closure (genSet A k), ∃ h ∈ Subgroup.closure (genSet A k),
      Red (m + 1) ((g * X * h : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) := by sorry
