-- Prove2me | Theorems.Thm_PI_WittUnramWork_sHom_coeff_zero
-- name    : PI.WittUnramWork.sHom_coeff_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:45:44.814204+00:00
-- url     : https://prove2.me/theorems/abc0c2d9-b6fe-4e1c-94cf-da5030d67991
-- title:
--   Witt Unram Work: s Hom coeff zero
-- statement:
--   The Witt Unram Work construction uses the s Hom coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/GhostComponentG.lean#L200-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittUnramified/GhostComponentG.lean#L200-L204

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

theorem PI.WittUnramWork.sHom_coeff_zero (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    (sHom p Qq F hF hinj x).coeff 0 = x := by sorry
