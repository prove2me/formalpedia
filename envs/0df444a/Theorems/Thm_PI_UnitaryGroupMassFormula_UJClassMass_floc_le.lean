-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_floc_le
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.floc_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:21:10.494458+00:00
-- url     : https://prove2.me/theorems/4feb7dfe-ab5b-5d15-9989-ba66909e0915
-- title:
--   UJClass Mass: floc le
-- statement:
--   The UJClass Mass construction uses the floc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L45-L50

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.floc_le (v : HeightOneSpectrum (𝓞 F)) (L N : Submodule (𝓞 E) V) (D : ℤ)
    (hD : ((D : 𝓞 F)) ∉ v.asIdeal) (hLN : ∀ x ∈ L, (D : 𝓞 E) • x ∈ N) : Floc v L ⊆ Floc v N := by sorry
