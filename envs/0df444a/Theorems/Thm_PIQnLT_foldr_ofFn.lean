-- Prove2me | Theorems.Thm_PIQnLT_foldr_ofFn
-- name    : PIQnLT.foldr_ofFn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:58.965548+00:00
-- url     : https://prove2.me/theorems/784f48e6-778b-4432-9a78-9f6bb1cb4715
-- title:
--   PIQn LT: foldr of Fn
-- statement:
--   The PIQn LT construction uses the foldr of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L134-L141

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_ExpLz
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
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

theorem PIQnLT.foldr_ofFn {α β : Type*} {t : ℕ} (R : α → β) (Tb : Fin t → α → α) (Ts : Fin t → β → β)
    (h : ∀ j G, R (Tb j G) = Ts j (R G)) (F : α) :
    R ((List.ofFn Tb).foldr (fun T h => T h) F) = (List.ofFn Ts).foldr (fun T h => T h) (R F) := by sorry
