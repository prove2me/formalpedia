-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_HX_tensInt_le
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.HX.tensInt_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:44:59.621666+00:00
-- url     : https://prove2.me/theorems/95ce0cca-f918-4bad-afb9-fc544fbdccc5
-- title:
--   HX: tens Int le
-- statement:
--   The HX construction uses the tens Int le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L37-L51

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.HX.tensInt_le (t : HeightOneSpectrum (𝓞 F)) {s : E ⊗[F] t.adicCompletion F}
    (hs : s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (t.adicCompletionIntegers F).toSubring) :
    s ∈ tensA (E := E) t := by sorry
