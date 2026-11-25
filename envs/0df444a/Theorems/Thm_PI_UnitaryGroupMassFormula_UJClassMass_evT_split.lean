-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_split
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.evT_split
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:20:47.142723+00:00
-- url     : https://prove2.me/theorems/344854ae-dbca-5a00-aedf-3df3de47bef6
-- title:
--   UJClass Mass: ev T split
-- statement:
--   The UJClass Mass construction uses the ev T split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/AlgebraMapIntIntAf.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/AlgebraMapIntIntAf.lean#L55-L63

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.evT_split {B S : Set (HeightOneSpectrum (𝓞 F))} (hBS : B ⊆ S) : evT S = evT B + evT (S \ B) := by sorry
