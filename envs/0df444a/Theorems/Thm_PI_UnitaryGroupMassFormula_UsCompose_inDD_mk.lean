-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_inDD_mk
-- name    : PI.UnitaryGroupMassFormula.UsCompose.inDD_mk
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:04:32.471803+00:00
-- url     : https://prove2.me/theorems/8e7b607b-f2d2-48e2-9614-ed26d396cc9b
-- title:
--   Us Compose: in DD mk
-- statement:
--   The Us Compose construction uses the in DD mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Development.lean#L136-L142

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem PI.UnitaryGroupMassFormula.UsCompose.inDD_mk {k j ρ κ o : ℕ} (L : FS k (j + ρ)) (h : Bd k j ρ κ o L) :
    InDD k j ρ o κ (L.map (mkTerm (Wp := Wp) (Wq := Wq) k j ρ)) := by sorry
