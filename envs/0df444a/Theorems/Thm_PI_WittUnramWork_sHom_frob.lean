-- Prove2me | Theorems.Thm_PI_WittUnramWork_sHom_frob
-- name    : PI.WittUnramWork.sHom_frob
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:36.142259+00:00
-- url     : https://prove2.me/theorems/a722f896-c50b-4c1c-b11a-981f5ef0be39
-- title:
--   Witt Unram Work: s Hom frob
-- statement:
--   The Witt Unram Work construction uses the s Hom frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/GhostComponentG.lean#L195-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/GhostComponentG.lean#L195-L198

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

theorem PI.WittUnramWork.sHom_frob (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    sHom p Qq F hF hinj (F x) = frobenius (sHom p Qq F hF hinj x) := by sorry
