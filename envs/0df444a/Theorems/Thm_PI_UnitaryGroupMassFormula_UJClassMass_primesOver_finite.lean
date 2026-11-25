-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_primesOver_finite
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.primesOver_finite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:42:54.277314+00:00
-- url     : https://prove2.me/theorems/b265c8e1-2d67-4da4-a4b1-45ba9bad4b7e
-- title:
--   UJClass Mass: primes Over finite
-- statement:
--   The UJClass Mass construction uses the primes Over finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjS.lean#L37-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjS.lean#L37-L54

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.primesOver_finite (T : Finset (HeightOneSpectrum (𝓞 F))) :
    {p : Ideal (𝓞 E) | p.IsMaximal ∧ ∃ v ∈ T, p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal}.Finite := by sorry
