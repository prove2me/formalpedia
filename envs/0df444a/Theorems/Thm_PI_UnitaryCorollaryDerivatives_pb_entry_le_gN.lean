-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_entry_le_gN
-- name    : PI.UnitaryCorollaryDerivatives.pb_entry_le_gN
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:23.52389+00:00
-- url     : https://prove2.me/theorems/3d09387a-90d9-5c41-abe3-aafeafc91669
-- title:
--   Unitary Corollary Derivatives: pb entry le g N
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb entry le g N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L18-L29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolyBB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.UnitaryCorollaryDerivatives.pb_entry_le_gN (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖M i j‖ ≤ B.gN M := by sorry
