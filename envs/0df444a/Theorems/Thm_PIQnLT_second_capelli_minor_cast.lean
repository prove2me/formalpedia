-- Prove2me | Theorems.Thm_PIQnLT_second_capelli_minor_cast
-- name    : PIQnLT.second_capelli_minor_cast
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:48:02.884869+00:00
-- url     : https://prove2.me/theorems/08a73c92-0f5d-5477-a28e-1acbaa3bee2f
-- title:
--   PIQn LT: second capelli minor cast
-- statement:
--   The PIQn LT construction uses the second capelli minor cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L183-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L183-L197

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (hL : LevHom)
include hL

theorem PIQnLT.second_capelli_minor_cast {t₁ t₂ : ℕ} (h : t₁ = t₂) (pos₁ : Fin t₁ → Fin (2 * (i + r') + k + 1))
    (pos₂ : Fin t₂ → Fin (2 * r' + k + 1)) (hpos : ∀ j, pos₁ j = levPos k i r' (pos₂ (Fin.cast h j))) (u : ℂ)
    (a a₁ β β₁ : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → Fin t₁ → ℂ)
    (a' a₁' β' β₁' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ → Fin t₂ → ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (ha : ∀ j, a (ιLev k i r' x) j = a' x (Fin.cast h j)) (ha₁ : ∀ j, a₁ (ιLev k i r' x) j = a₁' x (Fin.cast h j))
    (hb : ∀ j, β (ιLev k i r' x) j = β' x (Fin.cast h j)) (hb₁ : ∀ j, β₁ (ιLev k i r' x) j = β₁' x (Fin.cast h j)) :
    chat2L (Formalism.FourierDecayAlt.Q.EH k (i + r')) pos₁ u a a₁ β β₁ F (ιLev k i r' x) =
      chat2L (Formalism.FourierDecayAlt.Q.EH k r') pos₂ u a' a₁' β' β₁' (fun y => F (ιLev k i r' y)) x := by sorry
