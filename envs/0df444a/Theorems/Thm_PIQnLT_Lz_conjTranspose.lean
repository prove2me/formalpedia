-- Prove2me | Theorems.Thm_PIQnLT_Lz_conjTranspose
-- name    : PIQnLT.Lz_conjTranspose
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:55:19.127838+00:00
-- url     : https://prove2.me/theorems/cef06363-143d-4ad8-bc67-08a88344adc9
-- title:
--   PIQn LT: Lz conj Transpose
-- statement:
--   The PIQn LT construction uses the Lz conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/LzConjTranspose.lean#L72-L76

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

theorem PIQnLT.Lz_conjTranspose (W : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    (Lz k i r' W)ᴴ = Lz k i r' Wᴴ := by sorry
