-- Prove2me | Theorems.Thm_PIQnLT_pos_comp
-- name    : PIQnLT.pos_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:17:20.319793+00:00
-- url     : https://prove2.me/theorems/f084d04e-4da6-4298-9f03-5f7bdefae7c9
-- title:
--   PIQn LT: pos comp
-- statement:
--   The PIQn LT construction uses the pos comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L152-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L152-L155

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
omit hL

theorem PIQnLT.pos_comp {t : ℕ} (pos₁ : Fin t → Fin (2 * (i + r') + k + 1)) (pos₂ : Fin t → Fin (2 * r' + k + 1))
    (hpos : ∀ j, pos₁ j = levPos k i r' (pos₂ (Fin.cast rfl j))) : pos₁ = levPos k i r' ∘ pos₂ := by sorry
