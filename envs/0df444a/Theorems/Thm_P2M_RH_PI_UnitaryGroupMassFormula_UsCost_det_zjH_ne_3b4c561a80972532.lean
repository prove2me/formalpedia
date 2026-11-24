-- Prove2me | Theorems.Thm_P2M_RH_PI_UnitaryGroupMassFormula_UsCost_det_zjH_ne_3b4c561a80972532
-- name    : P2M_RH_PI_UnitaryGroupMassFormula_UsCost_det_zjH_ne_3b4c561a80972532
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:41.064478+00:00
-- url     : https://prove2.me/theorems/7ff8adfb-63f3-4ebe-8f88-c3a037e576b3
-- title:
--   P2 M RH PI Unitary Group Mass Formula Us Cost det zj H ne 3b4c561a80972532: P2 M RH PI Unitary Group Mass Formula Us Cost det zj H ne 3b4c561a80972532
-- statement:
--   The P2 M RH PI Unitary Group Mass Formula Us Cost det zj H ne 3b4c561a80972532 construction uses the P2 M RH PI Unitary Group Mass Formula Us Cost det zj H ne 3b4c561a80972532 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L149-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L149-L160

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}

theorem P2M_RH_PI_UnitaryGroupMassFormula_UsCost_det_zjH_ne_3b4c561a80972532 (hd : ∀ i, d i ≠ 0) (η : XiH p s σ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) :
    (ZjH σ d η Z).det ≠ 0 := by sorry

alias «PI».«UnitaryGroupMassFormula».«UsCost».«det_zjH_ne» := P2M_RH_PI_UnitaryGroupMassFormula_UsCost_det_zjH_ne_3b4c561a80972532
