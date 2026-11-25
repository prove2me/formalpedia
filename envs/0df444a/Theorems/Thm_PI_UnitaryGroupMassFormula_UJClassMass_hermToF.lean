-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_hermToF
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.hermToF
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:43:42.373801+00:00
-- url     : https://prove2.me/theorems/01ea4939-3161-4b4d-9eec-6b0bd779e675
-- title:
--   UJClass Mass: herm To F
-- statement:
--   The UJClass Mass construction uses the herm To F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjS.lean#L58-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjS.lean#L58-L88

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable [StarRing E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.hermToF (hst : ∀ a : F, star (algebraMap F E a) = algebraMap F E a)
    (v : HeightOneSpectrum (𝓞 F)) (X Y : Submodule (𝓞 E) V)
    (h : ∀ p : Ideal (𝓞 E), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal →
      loc (K := E) p X = loc (K := E) p Y) : Floc v X ⊆ Floc v Y := by sorry
