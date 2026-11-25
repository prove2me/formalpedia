-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_adT_idem
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.adT_idem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:30:30.478038+00:00
-- url     : https://prove2.me/theorems/99331ec0-4bc1-54cf-8fc4-e1b4a35d41e4
-- title:
--   UJClass Mass: ad T idem
-- statement:
--   The UJClass Mass construction uses the ad T idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PPatchF.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PPatchF.lean#L16-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PPatchF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassMass.adT_idem (T : Set (HeightOneSpectrum (𝓞 F))) : adT T * adT T = adT T := by sorry
