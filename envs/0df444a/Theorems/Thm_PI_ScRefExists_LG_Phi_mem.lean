-- Prove2me | Theorems.Thm_PI_ScRefExists_LG_Phi_mem
-- name    : PI.ScRefExists.LG.Phi_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:42:19.99569+00:00
-- url     : https://prove2.me/theorems/8aede7c2-c6da-51d3-9cf5-779905616bee
-- title:
--   LG: Phi mem
-- statement:
--   The LG construction uses the Phi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocGlob.lean#L44-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/LocGlob.lean#L44-L69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.LG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.ScRefExists.LG.Phi_mem (a : E) (ha : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈
    (algebraMap (𝓞 F) F).range) {y : E ⊗[F] Af F} (hy : y ∈ IntAf F E) :
    Phi a y ∈ Formalism.UG.intAd F := by sorry
