-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_unfolding_matrix_free_coordinate
-- name    : PI.TwistedEisensteinNonvanishing.W.unfolding_matrix_free_coordinate
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:30:27.494804+00:00
-- url     : https://prove2.me/theorems/4c7d8f71-5d05-408a-8be3-ba3ee1a416ab
-- title:
--   W: unfolding matrix free coordinate
-- statement:
--   The W construction uses the unfolding matrix free coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/UnfoldingMatrixFreeCoordinate.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/UnfoldingMatrixFreeCoordinate.lean#L43-L49

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]

theorem PI.TwistedEisensteinNonvanishing.W.unfolding_matrix_free_coordinate {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E) (p : FC n' c' n c) :
    xx1 y t (eN E (n' + c') p.1.2.1) p.1.1 = t p := by sorry
