-- Prove2me | Theorems.Thm_PI_SelfDualLoc_W_one_tmul_mem_Oloc
-- name    : PI.SelfDualLoc.W.one_tmul_mem_Oloc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:09.353342+00:00
-- url     : https://prove2.me/theorems/c52d64c1-0f17-493c-b669-dd964b01378c
-- title:
--   W: one tmul mem Oloc
-- statement:
--   The W construction uses the one tmul mem Oloc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/OneTmulMemOloc.lean#L41-L43

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

theorem PI.SelfDualLoc.W.one_tmul_mem_Oloc (v : HeightOneSpectrum (𝓞 F)) {b : v.adicCompletion F}
    (hb : b ∈ v.adicCompletionIntegers F) : (1 : E) ⊗ₜ[F] b ∈ Oloc F E v := by sorry
