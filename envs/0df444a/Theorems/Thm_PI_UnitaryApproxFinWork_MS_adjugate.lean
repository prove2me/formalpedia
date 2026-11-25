-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_MS_adjugate
-- name    : PI.UnitaryApproxFinWork.MS_adjugate
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:30:21.816663+00:00
-- url     : https://prove2.me/theorems/8cc0edce-8050-4d2f-9dd3-9c2ff80ec29e
-- title:
--   Unitary Approx Fin Work: MS adjugate
-- statement:
--   The Unitary Approx Fin Work construction uses the MS adjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/SigmaMemIntOE.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/SigmaMemIntOE.lean#L53-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_SigmaMemIntOE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open PI PI.UnitaryApproxFinWork
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n : Type} [Fintype n] [DecidableEq n]
variable {v : HeightOneSpectrum (𝓞 F)}

theorem PI.UnitaryApproxFinWork.MS_adjugate {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) :
    MS E v M.adjugate := by sorry
