-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_finMaxElt
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.finMaxElt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:11:26.930868+00:00
-- url     : https://prove2.me/theorems/b8f23118-7d1b-585e-8e07-f0b42cdeb409
-- title:
--   UJClass Mass: fin Max Elt
-- statement:
--   The UJClass Mass construction uses the fin Max Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjS.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/PSurjS.lean#L24-L35

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.finMaxElt (a : 𝓞 E) (ha : a ≠ 0) : {p : Ideal (𝓞 E) | p.IsMaximal ∧ a ∈ p}.Finite := by sorry
