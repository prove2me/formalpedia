-- Prove2me | Theorems.Thm_PI_SplitIntLoc_Proof_sup_dir
-- name    : PI.SplitIntLoc.Proof.sup_dir
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:10.79329+00:00
-- url     : https://prove2.me/theorems/e92b4b7b-c230-461c-bd28-c6804e69739b
-- title:
--   Proof: sup dir
-- statement:
--   The Proof construction uses the sup dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/ExistsUnitDiff.lean#L187-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/ExistsUnitDiff.lean#L187-L221

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

theorem PI.SplitIntLoc.Proof.sup_dir (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (x : E ⊗[F] (v.adicCompletion F))
    (h1 : (spl x).1 ∈ (v.adicCompletionIntegers F)) (h2 : (spl x).2 ∈ (v.adicCompletionIntegers F)) :
    x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring := by sorry
