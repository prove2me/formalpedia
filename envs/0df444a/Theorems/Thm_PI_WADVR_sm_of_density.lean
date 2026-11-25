-- Prove2me | Theorems.Thm_PI_WADVR_sm_of_density
-- name    : PI.WADVR.sm_of_density
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:43:07.682408+00:00
-- url     : https://prove2.me/theorems/eb1b61c0-3373-4468-9a8c-fcc4e2ddbbfc
-- title:
--   WADVR: sm of density
-- statement:
--   The WADVR construction uses the sm of density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L143-L147

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WADVR
variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]
variable {ϖ : W}

theorem PI.WADVR.sm_of_density (hϖ : Irreducible ϖ) {p : ℕ} (hp : ¬ IsUnit (p : W)) {y x : Q} {N : ℕ}
    {c : W} (h : y = x + (p : Q) ^ N * algebraMap W Q c) : Sm Q ϖ N (y - x) := by sorry
