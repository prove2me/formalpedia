-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_epsT_idem
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.epsT_idem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:04:28.025005+00:00
-- url     : https://prove2.me/theorems/5cf5518c-062f-4eb3-abd3-b90a19fd37f2
-- title:
--   UJClass Mass: eps T idem
-- statement:
--   The UJClass Mass construction uses the eps T idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PPatchF.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PPatchF.lean#L24-L26

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.epsT_idem (T : Set (HeightOneSpectrum (𝓞 F))) : epsT E T * epsT E T = epsT E T := by sorry
