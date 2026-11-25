-- Prove2me | Theorems.Thm_PI_SplitIntLoc_Proof_emb_algebraMap
-- name    : PI.SplitIntLoc.Proof.emb_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:52.561628+00:00
-- url     : https://prove2.me/theorems/9f463a5b-b552-4833-9bcf-1d0e0f236be9
-- title:
--   Proof: emb algebra Map
-- statement:
--   The Proof construction uses the emb algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L40-L44

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

theorem PI.SplitIntLoc.Proof.emb_algebraMap (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F))
    (hp : ∀ a, p (a, a) = a) (f : F) : emb spl p (algebraMap F E f) = algebraMap F (v.adicCompletion F) f := by sorry
