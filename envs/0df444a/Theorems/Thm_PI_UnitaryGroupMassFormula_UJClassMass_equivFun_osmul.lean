-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_equivFun_osmul
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.equivFun_osmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:48.659135+00:00
-- url     : https://prove2.me/theorems/864d4fbb-5e07-4863-b5ed-a043cb6eb329
-- title:
--   UJClass Mass: equiv Fun osmul
-- statement:
--   The UJClass Mass construction uses the equiv Fun osmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSSkeleton.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/LSSkeleton.lean#L53-L55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
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
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.equivFun_osmul {M : ℕ} (b : Module.Basis (Fin M) E V) (s : 𝓞 E) (v : V) :
    b.equivFun (s • v) = (algebraMap (𝓞 E) E s) • b.equivFun v := by sorry
