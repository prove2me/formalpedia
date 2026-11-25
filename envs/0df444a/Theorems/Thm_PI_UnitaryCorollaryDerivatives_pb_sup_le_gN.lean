-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_pb_sup_le_gN
-- name    : PI.UnitaryCorollaryDerivatives.pb_sup_le_gN
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:43.724058+00:00
-- url     : https://prove2.me/theorems/1de1d3cc-1edb-57d9-9ff7-264d551ae66e
-- title:
--   Unitary Corollary Derivatives: pb sup le g N
-- statement:
--   The Unitary Corollary Derivatives construction uses the pb sup le g N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/PolyBB.lean#L31-L33

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

theorem PI.UnitaryCorollaryDerivatives.pb_sup_le_gN (g : B.Mat k r) : ‖g‖ ≤ B.gN g := by sorry
