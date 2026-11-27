-- Prove2me | Theorems.Thm_PIW_AdelClassFin_star_fixed_reps
-- name    : PIW.AdelClassFin.star_fixed_reps
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:49:29.588112+00:00
-- url     : https://prove2.me/theorems/91deb2d6-9029-4262-89ec-a473e940abe3
-- title:
--   Adel Class Fin: star fixed reps
-- statement:
--   The Adel Class Fin construction uses the star fixed reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/IdealMulPrincipal.lean#L22-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/IdealMulPrincipal.lean#L22-L52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open NumberField
open scoped nonZeroDivisors

theorem PIW.AdelClassFin.star_fixed_reps (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) :
    ∃ R : Set E, R.Finite ∧ (N ≠ 0 → ∀ β : 𝓞 E, star (algebraMap (𝓞 E) E β) = algebraMap (𝓞 E) E β →
      ∃ r ∈ R, ∃ s : 𝓞 E, algebraMap (𝓞 E) E β = r + N * algebraMap (𝓞 E) E s ∧
        star (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s) := by sorry
