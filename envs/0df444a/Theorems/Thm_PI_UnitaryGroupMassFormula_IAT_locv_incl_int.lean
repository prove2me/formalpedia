-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_IAT_locv_incl_int
-- name    : PI.UnitaryGroupMassFormula.IAT.locv_incl_int
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:39:56.82532+00:00
-- url     : https://prove2.me/theorems/ae423ea2-8460-438e-be41-d5b2bd4c050c
-- title:
--   IAT: locv incl int
-- statement:
--   The IAT construction uses the locv incl int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralityAtPrimeLattices/AwayLoc.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IntegralityAtPrimeLattices/AwayLoc.lean#L16-L19

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

theorem PI.UnitaryGroupMassFormula.IAT.locv_incl_int (v : HeightOneSpectrum (𝓞 F)) (e : E) (he : IsIntegral ℤ e) :
    Formalism.UG.inclE (F := F) (v.adicCompletion F) e ∈ Formalism.L2.Geo.Def.PC.SV E v := by sorry
