-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Cj_rowT_mul_apply
-- name    : PI.VolSemiDirect.W.Cj.rowT_mul_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:36:32.099025+00:00
-- url     : https://prove2.me/theorems/73253d8a-be8c-57c5-9cf9-2e9c7571f5c7
-- title:
--   Cj: row T mul apply
-- statement:
--   The Cj construction uses the row T mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L80-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/GlGeneratedTransvectionsDiag.lean#L80-L89

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

theorem PI.VolSemiDirect.W.Cj.rowT_mul_apply (p : Fin k) (c : Fin k → A) (s : Finset (Fin k))
    (X : Matrix (Fin k) (Fin k) A) (a b : Fin k) :
    ((1 + ∑ i ∈ s, single p i (c i)) * X) a b =
      X a b + if a = p then ∑ i ∈ s, c i * X i b else 0 := by sorry
