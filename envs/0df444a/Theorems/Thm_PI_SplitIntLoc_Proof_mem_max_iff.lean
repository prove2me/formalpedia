-- Prove2me | Theorems.Thm_PI_SplitIntLoc_Proof_mem_max_iff
-- name    : PI.SplitIntLoc.Proof.mem_max_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:24:13.531077+00:00
-- url     : https://prove2.me/theorems/55c8dd92-de43-563f-889e-6469c186ed88
-- title:
--   Proof: mem max iff
-- statement:
--   The Proof construction uses the mem max iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L17-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
noncomputable section
open PI PI.SplitIntLoc PI.SplitIntLoc.Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem PI.SplitIntLoc.Proof.mem_max_iff (z : (v.adicCompletionIntegers F)) : z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ Valued.v (z : (v.adicCompletion F)) < 1 := by sorry
