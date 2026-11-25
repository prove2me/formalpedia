-- Prove2me | Theorems.Thm_PI_SplitIntLoc_Proof_exists_unit_diff
-- name    : PI.SplitIntLoc.Proof.exists_unit_diff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:24:59.070497+00:00
-- url     : https://prove2.me/theorems/731cb621-0b22-5d71-94af-5655879819ef
-- title:
--   Proof: exists unit diff
-- statement:
--   The Proof construction uses the exists unit diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/ExistsUnitDiff.lean#L164-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitPrimeIntegers/ExistsUnitDiff.lean#L164-L185

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

theorem PI.SplitIntLoc.Proof.exists_unit_diff (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ b : 𝓞 E, IsUnit (phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) b - phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b) := by sorry
