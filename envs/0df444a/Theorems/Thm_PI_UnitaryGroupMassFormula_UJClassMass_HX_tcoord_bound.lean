-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_HX_tcoord_bound
-- name    : PI.UnitaryGroupMassFormula.UJClassMass.HX.tcoord_bound
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:23:40.435693+00:00
-- url     : https://prove2.me/theorems/dc1d55b9-2560-4cee-9bb7-c2bd678341af
-- title:
--   HX: tcoord bound
-- statement:
--   The HX construction uses the tcoord bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L65-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean#L65-L91

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

theorem PI.UnitaryGroupMassFormula.UJClassMass.HX.tcoord_bound {ι : Type} (B : Module.Basis ι F E) (m : ℤ)
    (hm : ∀ x ∈ PI.UnitaryApproxDefs.intOE E, ∀ k, IsIntegral ℤ ((m : F) * B.coord k x)) (t : HeightOneSpectrum (𝓞 F))
    (c : 𝓞 F) (k : ι) {s : E ⊗[F] t.adicCompletion F} (hs : s ∈ tensA (E := E) t) :
    ∃ u ∈ t.adicCompletionIntegers F, (m : t.adicCompletion F) *
        tcoord B k (t.adicCompletion F) (PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (c : F)) * s) =
      algebraMap F (t.adicCompletion F) (c : F) * u := by sorry
