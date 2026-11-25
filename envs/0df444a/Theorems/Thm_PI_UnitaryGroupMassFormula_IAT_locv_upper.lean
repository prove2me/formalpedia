-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IAT_locv_upper
-- name    : PI.UnitaryGroupMassFormula.IAT.locv_upper
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:54.982575+00:00
-- url     : https://prove2.me/theorems/350538df-750b-488e-9021-8057b0b1cf5a
-- title:
--   IAT: locv upper
-- statement:
--   The IAT construction uses the locv upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralityAtPrimeLattices/AwayLoc.lean#L21-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralityAtPrimeLattices/AwayLoc.lean#L21-L53

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

theorem PI.UnitaryGroupMassFormula.IAT.locv_upper (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ z ∈ Formalism.L2.Geo.Def.PC.latV v Λ, ∀ i,
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (m : E) * z i ∈ Formalism.L2.Geo.Def.PC.SV E v := by sorry
