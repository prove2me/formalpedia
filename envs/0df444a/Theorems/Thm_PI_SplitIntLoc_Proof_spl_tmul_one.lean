-- Prove2me | Theorems.Thm_PI_SplitIntLoc_Proof_spl_tmul_one
-- name    : PI.SplitIntLoc.Proof.spl_tmul_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:01.789189+00:00
-- url     : https://prove2.me/theorems/0cc6fbd4-ba2a-4e05-972a-d7bd33828b89
-- title:
--   Proof: spl tmul one
-- statement:
--   The Proof construction uses the spl tmul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L37-L38

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

theorem PI.SplitIntLoc.Proof.spl_tmul_one (e : E) :
    spl (e ⊗ₜ[F] 1) = (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) e, emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) e) := by sorry
