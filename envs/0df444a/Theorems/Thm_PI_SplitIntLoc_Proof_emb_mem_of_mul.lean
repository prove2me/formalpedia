-- Prove2me | Theorems.Thm_PI_SplitIntLoc_Proof_emb_mem_of_mul
-- name    : PI.SplitIntLoc.Proof.emb_mem_of_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:24:53.925427+00:00
-- url     : https://prove2.me/theorems/1f9ed287-4b4c-51a8-9301-c41f00354d0f
-- title:
--   Proof: emb mem of mul
-- statement:
--   The Proof construction uses the emb mem of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/ExistsUnitDiff.lean#L104-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/ExistsUnitDiff.lean#L104-L117

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
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
  {v : HeightOneSpectrum (𝓞 F)} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))

theorem PI.SplitIntLoc.Proof.emb_mem_of_mul (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (a s : 𝓞 E) (hs : s ∉ P spl p) (z : E)
    (hz : z * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a) : emb spl p z ∈ (v.adicCompletionIntegers F) := by sorry
