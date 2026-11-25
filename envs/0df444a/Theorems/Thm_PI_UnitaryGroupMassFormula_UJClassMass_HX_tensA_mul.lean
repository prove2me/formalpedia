-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_HX_tensA_mul
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.HX.tensA_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:49:03.27584+00:00
-- url     : https://prove2.me/theorems/756b9e5c-0d04-51b8-ae23-07640f1a309a
-- title:
--   HX: tens A mul
-- statement:
--   The HX construction uses the tens A mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L19-L35

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_TcoordBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
open PI.UnitaryGroupMassFormula.UJClassMass.HX
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.UnitaryGroupMassFormula.UJClassMass.HX.tensA_mul (t : HeightOneSpectrum (𝓞 F)) {a b : E ⊗[F] t.adicCompletion F}
    (ha : a ∈ tensA (E := E) t) (hb : b ∈ tensA (E := E) t) : a * b ∈ tensA (E := E) t := by sorry
