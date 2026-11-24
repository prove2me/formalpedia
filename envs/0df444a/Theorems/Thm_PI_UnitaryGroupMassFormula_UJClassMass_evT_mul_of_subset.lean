-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_mul_of_subset
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.evT_mul_of_subset
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:52:18.293894+00:00
-- url     : https://prove2.me/theorems/f26bd725-a3c2-4bd4-8e81-9be834c5801d
-- title:
--   UJClass Mass: ev T mul of subset
-- statement:
--   The UJClass Mass construction uses the ev T mul of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/AlgebraMapIntIntAf.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/AlgebraMapIntIntAf.lean#L47-L53

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_AlgebraMapIntIntAf
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
variable {F : Type} [Field F] [NumberField F]

theorem PI.UnitaryGroupMassFormula.UJClassMass.evT_mul_of_subset {X Y : Set (HeightOneSpectrum (𝓞 F))} (hXY : X ⊆ Y) : evT X * evT Y = evT X := by sorry
