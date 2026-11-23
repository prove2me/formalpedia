-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equivFun_linOf
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.equivFun_linOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:54.892807+00:00
-- url     : https://prove2.me/theorems/c66c3a8b-46cc-44b5-af7f-f639c4ab0429
-- title:
--   UJClass Mass: equiv Fun lin Of
-- statement:
--   The UJClass Mass construction uses the equiv Fun lin Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/EquivFunLinOf.lean#L56-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/EquivFunLinOf.lean#L56-L65

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.equivFun_linOf {M : ℕ} (b : Module.Basis (Fin M) E V) (u : GL (Fin M) E) (v : V) :
    b.equivFun (linOf b u v) = (u : Matrix (Fin M) (Fin M) E).mulVec (b.equivFun v) := by sorry
