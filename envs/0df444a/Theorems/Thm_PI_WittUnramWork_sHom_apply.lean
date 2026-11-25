-- Prove2me | Theorems.Thm_PI_WittUnramWork_sHom_apply
-- name    : PI.WittUnramWork.sHom_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:43.221575+00:00
-- url     : https://prove2.me/theorems/29a3e1a5-52e4-4293-b415-bd834216ffea
-- title:
--   Witt Unram Work: s Hom apply
-- statement:
--   The Witt Unram Work construction uses the s Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/GhostComponentG.lean#L175-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/GhostComponentG.lean#L175-L176

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_GhostComponentG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
variable (p Qq) [Invertible (p : Qq)] (F : W →+* W)
variable (hF : ∀ x : W, ∃ y : W, F x = x ^ p + (p : W) * y)
include hF

theorem PI.WittUnramWork.sHom_apply (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    sHom p Qq F hF hinj x = sFun p Qq F hF hinj x := by sorry
