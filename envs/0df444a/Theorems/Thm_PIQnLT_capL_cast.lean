-- Prove2me | Theorems.Thm_PIQnLT_capL_cast
-- name    : PIQnLT.capL_cast
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:25.465509+00:00
-- url     : https://prove2.me/theorems/87ed7dc1-82d4-4b02-8a7c-0bea0298aa14
-- title:
--   PIQn LT: cap L cast
-- statement:
--   The PIQn LT construction uses the cap L cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L157-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L157-L167

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

theorem PIQnLT.capL_cast {t₁ t₂ : ℕ} (h : t₁ = t₂) (pos₁ : Fin t₁ → Fin (2 * (i + r') + k + 1))
    (pos₂ : Fin t₂ → Fin (2 * r' + k + 1)) (hpos : ∀ j, pos₁ j = levPos k i r' (pos₂ (Fin.cast h j))) (u : ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    qminorOp (Formalism.FourierDecayAlt.Q.EH k (i + r')) pos₁ pos₁ u F (ιLev k i r' x) =
      qminorOp (Formalism.FourierDecayAlt.Q.EH k r') pos₂ pos₂ u (fun y => F (ιLev k i r' y)) x := by sorry
