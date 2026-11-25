-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_theta_int
-- name    : PI.ParahoricIdxZ.W.theta_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:54.743646+00:00
-- url     : https://prove2.me/theorems/1588c655-f2a3-577b-8861-d65892db0282
-- title:
--   W: theta int
-- statement:
--   The W construction uses the theta int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L64-L73

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

theorem PI.ParahoricIdxZ.W.theta_int {a t : ℕ} {A : Matrix (Fin a) (Fin a) F} {B : Matrix (Fin a) (Fin t) F}
    {C : Matrix (Fin t) (Fin a) F} {D : Matrix (Fin t) (Fin t) F}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (hC : ∀ i j, C i j ∈ O)
    (hD : ∀ i j, D i j ∈ O) : Formalism.DoubleCosetMeasures.IsInt O (theta A B C D) := by sorry
