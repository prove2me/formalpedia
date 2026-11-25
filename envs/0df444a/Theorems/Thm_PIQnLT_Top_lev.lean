-- Prove2me | Theorems.Thm_PIQnLT_Top_lev
-- name    : PIQnLT.Top_lev
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:44.861942+00:00
-- url     : https://prove2.me/theorems/f83e0b2c-9692-4bf5-b557-a763ed5a003c
-- title:
--   PIQn LT: Top lev
-- statement:
--   The PIQn LT construction uses the Top lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L124-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L124-L131

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

theorem PIQnLT.Top_lev (u : ℂ) (a b : Fin (2 * r' + k + 1))
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k (i + r')) u (levPos k i r' a) (levPos k i r' b) F (ιLev k i r' x) =
      Formalism.QuantumDeterminants.Top (Formalism.FourierDecayAlt.Q.EH k r') u a b (fun y => F (ιLev k i r' y)) x := by sorry
