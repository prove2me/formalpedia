-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_theta_apply
-- name    : PI.ParahoricIdxZ.W.theta_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:16.941331+00:00
-- url     : https://prove2.me/theorems/922a387d-4fd5-4fa0-a863-8967d9013847
-- title:
--   W: theta apply
-- statement:
--   The W construction uses the theta apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L32-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

theorem PI.ParahoricIdxZ.W.theta_apply {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R)
    (B : Matrix (Fin a) (Fin t) R) (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R)
    (x y : Fin a ⊕ Fin t) :
    theta A B C D (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.fromBlocks A B C D x y := by sorry
