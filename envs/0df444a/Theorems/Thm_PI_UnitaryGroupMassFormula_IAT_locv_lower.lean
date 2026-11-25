-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IAT_locv_lower
-- name    : PI.UnitaryGroupMassFormula.IAT.locv_lower
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:58.633289+00:00
-- url     : https://prove2.me/theorems/8ba59299-c7c4-4186-9fef-17b2b9fc57d2
-- title:
--   IAT: locv lower
-- statement:
--   The IAT construction uses the locv lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralityAtPrimeLattices/AwayLoc.lean#L55-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralityAtPrimeLattices/AwayLoc.lean#L55-L96

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralityAtPrimeLattices_AwayLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IAT
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem PI.UnitaryGroupMassFormula.IAT.locv_lower (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ w : Fin n → E ⊗[F] v.adicCompletion F, (∀ i, w i ∈ Formalism.L2.Geo.Def.PC.SV E v) →
      (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) (m : E) * w i) ∈ Formalism.L2.Geo.Def.PC.latV v Λ := by sorry
