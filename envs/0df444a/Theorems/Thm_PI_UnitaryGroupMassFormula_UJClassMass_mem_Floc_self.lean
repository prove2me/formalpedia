-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_mem_Floc_self
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.mem_Floc_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:35.275098+00:00
-- url     : https://prove2.me/theorems/110b0403-ca6d-5841-8377-85ede85d8155
-- title:
--   UJClass Mass: mem Floc self
-- statement:
--   The UJClass Mass construction uses the mem Floc self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L41-L43

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSSkeleton
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {V : Type}
  [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.mem_Floc_self (v : HeightOneSpectrum (𝓞 F)) (X : Submodule (𝓞 E) V) {x : V} (hx : x ∈ X) :
    x ∈ Floc v X := by sorry
