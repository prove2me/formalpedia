-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UsCost_rn_mem__52f76f729929
-- name    : P2M_PI_UnitaryGroupMassFormula_UsCost_rn_mem__52f76f729929
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:56.368737+00:00
-- url     : https://prove2.me/theorems/871cf5ae-aee1-4acd-bcac-53349151b486
-- title:
--   P2 M PI Unitary Group Mass Formula Us Cost rn mem  52f76f729929: P2 M PI Unitary Group Mass Formula Us Cost rn mem  52f76f729929
-- statement:
--   The P2 M PI Unitary Group Mass Formula Us Cost rn mem  52f76f729929 construction uses the P2 M PI Unitary Group Mass Formula Us Cost rn mem  52f76f729929 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L162-L164

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

theorem P2M_PI_UnitaryGroupMassFormula_UsCost_rn_mem__52f76f729929 (hRP : RadicalParam) (j : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by sorry

alias «PI».«UnitaryGroupMassFormula».«UsCost».«rn_mem'» := P2M_PI_UnitaryGroupMassFormula_UsCost_rn_mem__52f76f729929
