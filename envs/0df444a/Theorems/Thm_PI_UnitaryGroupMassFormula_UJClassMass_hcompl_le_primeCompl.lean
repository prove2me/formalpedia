-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_hcompl_le_primeCompl
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.hcompl_le_primeCompl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:42:33.345052+00:00
-- url     : https://prove2.me/theorems/f3124e5f-c799-4b11-96bd-b5dfc7c25fa3
-- title:
--   UJClass Mass: hcompl le prime Compl
-- statement:
--   The UJClass Mass construction uses the hcompl le prime Compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjH.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjH.lean#L24-L26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem PI.UnitaryGroupMassFormula.UJClassMass.hcompl_le_primeCompl (p : Ideal (𝓞 E)) [p.IsPrime] : hcompl (K := E) p ≤ p.primeCompl := by sorry
