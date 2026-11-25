-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_interLocF
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.interLocF
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:42:30.105674+00:00
-- url     : https://prove2.me/theorems/2445faab-7cee-4d94-b936-b1a59f5b8379
-- title:
--   UJClass Mass: inter Loc F
-- statement:
--   The UJClass Mass construction uses the inter Loc F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L100-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L100-L111

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.interLocF [FiniteDimensional E V] (N : Submodule (𝓞 E) V) (hN : Submodule.IsLattice E N) (x : V)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F), x ∈ Floc v N) : x ∈ N := by sorry
