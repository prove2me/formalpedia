-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_det_mem
-- name    : PI.UnitaryApproxFinWork.det_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:05.538357+00:00
-- url     : https://prove2.me/theorems/f9a91a42-d9a6-4056-92bd-40eddce40faf
-- title:
--   Unitary Approx Fin Work: det mem
-- statement:
--   The Unitary Approx Fin Work construction uses the det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/SigmaMemIntOE.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/SigmaMemIntOE.lean#L59-L61

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

theorem PI.UnitaryApproxFinWork.det_mem {M : Matrix n n (E ⊗[F] v.adicCompletion F)} (hM : MS E v M) : M.det ∈ Sv E v := by sorry
