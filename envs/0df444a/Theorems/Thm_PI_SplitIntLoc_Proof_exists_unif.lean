-- Prove2me | Theorems.Thm_PI_SplitIntLoc_Proof_exists_unif
-- name    : PI.SplitIntLoc.Proof.exists_unif
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:58.003798+00:00
-- url     : https://prove2.me/theorems/d12443f7-8255-4b30-8792-cfad6615a7e2
-- title:
--   Proof: exists unif
-- statement:
--   The Proof construction uses the exists unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L21-L28

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

theorem PI.SplitIntLoc.Proof.exists_unif : ∃ π : 𝓞 F, (algebraMap (𝓞 F) F π) ≠ 0 ∧
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F π)) < 1 := by sorry
