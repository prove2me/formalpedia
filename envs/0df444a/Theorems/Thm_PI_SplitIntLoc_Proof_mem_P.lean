-- Prove2me | Theorems.Thm_PI_SplitIntLoc_Proof_mem_P
-- name    : PI.SplitIntLoc.Proof.mem_P
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:24:08.084444+00:00
-- url     : https://prove2.me/theorems/7ce1edcc-1701-5440-8228-9dab7f41ae13
-- title:
--   Proof: mem P
-- statement:
--   The Proof construction uses the mem P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L67-L70

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
variable {v} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))

theorem PI.SplitIntLoc.Proof.mem_P (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (z : 𝓞 E) :
    z ∈ P spl p ↔ Valued.v (emb spl p (algebraMap (𝓞 E) E z)) < 1 := by sorry
