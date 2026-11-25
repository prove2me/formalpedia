-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_flocEq
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.flocEq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:42:43.927088+00:00
-- url     : https://prove2.me/theorems/8b1ca917-ab4e-4c34-9b1e-769dc489f8d5
-- title:
--   UJClass Mass: floc Eq
-- statement:
--   The UJClass Mass construction uses the floc Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L52-L55

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.flocEq (v : HeightOneSpectrum (𝓞 F)) (L N : Submodule (𝓞 E) V) (D : ℤ)
    (hD : ((D : 𝓞 F)) ∉ v.asIdeal) (hLN : ∀ x ∈ L, (D : 𝓞 E) • x ∈ N) (hNL : ∀ x ∈ N, (D : 𝓞 E) • x ∈ L) :
    Floc v L = Floc v N := by sorry
