-- Prove2me | Theorems.Thm_PIQnLT_chatL_lev
-- name    : PIQnLT.chatL_lev
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:58.350499+00:00
-- url     : https://prove2.me/theorems/987e5500-97c5-4e68-a50c-624262208478
-- title:
--   PIQn LT: chat L lev
-- statement:
--   The PIQn LT construction uses the chat L lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L119-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L119-L131

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

theorem PIQnLT.chatL_lev {t : ℕ} (pos : Fin t → Fin (2 * r' + k + 1)) (u : ℂ)
    (a β : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → Fin t → ℂ)
    (a' β' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ → Fin t → ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (ha : a (ιLev k i r' x) = a' x) (hb : β (ιLev k i r' x) = β' x) :
    chatL (Formalism.FourierDecayAlt.Q.EH k (i + r')) (levPos k i r' ∘ pos) u a β F (ιLev k i r' x) =
      chatL (Formalism.FourierDecayAlt.Q.EH k r') pos u a' β' (fun y => F (ιLev k i r' y)) x := by sorry
