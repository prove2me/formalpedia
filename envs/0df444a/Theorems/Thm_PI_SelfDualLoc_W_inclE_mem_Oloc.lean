-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_inclE_mem_Oloc
-- name    : PI.SelfDualLoc.W.inclE_mem_Oloc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:44.146642+00:00
-- url     : https://prove2.me/theorems/ce082ce1-b5be-4428-ada1-104564e5b44f
-- title:
--   W: incl E mem Oloc
-- statement:
--   The W construction uses the incl E mem Oloc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L36-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [NumberField F] [NumberField E]

theorem PI.SelfDualLoc.W.inclE_mem_Oloc (v : HeightOneSpectrum (𝓞 F)) {e : E} (he : e ∈ intOE E) :
    inclE (F := F) (v.adicCompletion F) e ∈ Oloc F E v := by sorry
