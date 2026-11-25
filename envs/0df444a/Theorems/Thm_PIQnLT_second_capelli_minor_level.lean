-- Prove2me | Theorems.Thm_PIQnLT_second_capelli_minor_level
-- name    : PIQnLT.second_capelli_minor_level
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:04:23.884904+00:00
-- url     : https://prove2.me/theorems/c895a843-d342-4810-92ef-5d4b57ff70d2
-- title:
--   PIQn LT: second capelli minor level
-- statement:
--   The PIQn LT construction uses the second capelli minor level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L133-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L133-L149

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

theorem PIQnLT.second_capelli_minor_level {t : ℕ} (pos : Fin t → Fin (2 * r' + k + 1)) (u : ℂ)
    (a a₁ β β₁ : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → Fin t → ℂ)
    (a' a₁' β' β₁' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ → Fin t → ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (ha : a (ιLev k i r' x) = a' x) (ha₁ : a₁ (ιLev k i r' x) = a₁' x)
    (hb : β (ιLev k i r' x) = β' x) (hb₁ : β₁ (ιLev k i r' x) = β₁' x) :
    chat2L (Formalism.FourierDecayAlt.Q.EH k (i + r')) (levPos k i r' ∘ pos) u a a₁ β β₁ F (ιLev k i r' x) =
      chat2L (Formalism.FourierDecayAlt.Q.EH k r') pos u a' a₁' β' β₁' (fun y => F (ιLev k i r' y)) x := by sorry
