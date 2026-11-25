-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_unfolding_matrix_sub
-- name    : PI.TwistedEisensteinNonvanishing.W.unfolding_matrix_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:30:05.954146+00:00
-- url     : https://prove2.me/theorems/21f99787-4ec8-4c3a-a296-96cc83f96565
-- title:
--   W: unfolding matrix sub
-- statement:
--   The W construction uses the unfolding matrix sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/UnfoldingMatrixFreeCoordinate.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/UnfoldingMatrixFreeCoordinate.lean#L62-L69

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

theorem PI.TwistedEisensteinNonvanishing.W.unfolding_matrix_sub {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t t' : FC n' c' n c → E) (s : ℕ) (l : Fin (n + c)) :
    (xx1 y t - xx1 y t') (eN E (n' + c') s) l =
      if hs : s < n' + c' then (if hf : IsFree n' n c l.1 s then t ⟨(l, ⟨s, hs⟩), hf⟩ - t' ⟨(l, ⟨s, hs⟩), hf⟩ else 0) else 0 := by sorry
