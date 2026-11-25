-- Prove2me | Theorems.Thm_PI_FJMB_aeval_translate_eq
-- name    : PI.FJMB.aeval_translate_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:42.099147+00:00
-- url     : https://prove2.me/theorems/4ccc8b32-e01f-5526-a0d4-1c58c7716c95
-- title:
--   FJMB: aeval translate eq
-- statement:
--   The FJMB construction uses the aeval translate eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurChain.lean#L54-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurChain.lean#L54-L99

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMB
variable {R : Type*} [CommRing R] {σ : Type*}

theorem PI.FJMB.aeval_translate_eq {K : Type*} [Field K] [CharZero K] [Algebra R K] (f : MvPolynomial σ R)
    (S : Finset σ) (c : σ → MvPolynomial σ R) (hf : ∑ v ∈ S, c v * pderiv v f = 0) (y z : σ → K)
    (hz : ∀ v, v ∉ S → z v = 0)
    (hc : ∀ v ∈ S, aeval (fun w => Polynomial.C (y w) + Polynomial.X * Polynomial.C (z w)) (c v) =
      Polynomial.C (z v)) (t : K) :
    aeval (fun w => y w + t * z w) f = aeval y f := by sorry
