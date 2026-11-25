-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_one_symm_apply
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.linOf_one_symm_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:38:56.196421+00:00
-- url     : https://prove2.me/theorems/7c8fbab2-7235-53c6-8c83-48c5caa29a99
-- title:
--   UJClass Mass: lin Of one symm apply
-- statement:
--   The UJClass Mass construction uses the lin Of one symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjP.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjP.lean#L28-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass

theorem PI.UnitaryGroupMassFormula.UJClassMass.linOf_one_symm_apply {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (v : V) : (linOf b (1 : GL (Fin M) E)).symm v = v := by sorry
