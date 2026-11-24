-- Prove2me | Theorems.Thm_P2M_PIQnLT__Lev_inv_f9be2b119148
-- name    : P2M_PIQnLT__Lev_inv_f9be2b119148
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:39:19.326543+00:00
-- url     : https://prove2.me/theorems/6ce50e5d-72fa-41c1-8413-34b7aef71781
-- title:
--   P2 M PIQn LT  Lev inv f9be2b119148: P2 M PIQn LT  Lev inv f9be2b119148
-- statement:
--   The P2 M PIQn LT  Lev inv f9be2b119148 construction uses the P2 M PIQn LT  Lev inv f9be2b119148 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelTransfer/SecondCapelliMinorLevel.lean#L102-L104

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

theorem P2M_PIQnLT__Lev_inv_f9be2b119148 (hL : LevHom) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (hg : IsUnit g.det) :
    (ιLev k i r' g)⁻¹ = ιLev k i r' g⁻¹ := by sorry

alias «PIQnLT».«ιLev_inv» := P2M_PIQnLT__Lev_inv_f9be2b119148
