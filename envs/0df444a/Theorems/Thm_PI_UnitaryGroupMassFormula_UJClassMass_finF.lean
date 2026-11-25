-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_finF
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.finF
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:42:23.744413+00:00
-- url     : https://prove2.me/theorems/f34799d1-37c3-4722-8120-329677c2032f
-- title:
--   UJClass Mass: fin F
-- statement:
--   The UJClass Mass construction uses the fin F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjF.lean#L58-L67

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
omit [NumberField E]

theorem PI.UnitaryGroupMassFormula.UJClassMass.finF (D : ℤ) (hD : D ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ((D : 𝓞 F)) ∈ v.asIdeal}.Finite := by sorry
