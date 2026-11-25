-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_reduce
-- name    : PI.VolSemiDirect.W.Cj.reduce
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:16.090798+00:00
-- url     : https://prove2.me/theorems/c4efe8ff-1833-510d-aed2-8d34d916ca92
-- title:
--   Cj: reduce
-- statement:
--   The Cj construction uses the reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L280-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L280-L304

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

theorem PI.VolSemiDirect.W.Cj.reduce (hA : HasStableRangeOne A) : ∀ n : ℕ, ∀ X : GL (Fin k) A,
    Red (k - n) (X : Matrix (Fin k) (Fin k) A) → X ∈ Subgroup.closure (genSet A k) := by sorry
