-- Prove2me | Theorems.Thm_PI_SplitIntLoc_Proof_sub_dir
-- name    : PI.SplitIntLoc.Proof.sub_dir
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:23:38.3098+00:00
-- url     : https://prove2.me/theorems/fb8d0ace-e0d5-512d-9661-98151d81ccac
-- title:
--   Proof: sub dir
-- statement:
--   The Proof construction uses the sub dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L86-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/EmbMemOfIsIntegral.lean#L86-L105

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

theorem PI.SplitIntLoc.Proof.sub_dir (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (x : E ⊗[F] (v.adicCompletion F))
    (hx : x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring) :
    (spl x).1 ∈ (v.adicCompletionIntegers F) ∧ (spl x).2 ∈ (v.adicCompletionIntegers F) := by sorry
