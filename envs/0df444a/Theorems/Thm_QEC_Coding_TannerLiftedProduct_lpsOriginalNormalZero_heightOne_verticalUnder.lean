-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalZero_heightOne_verticalUnder
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_heightOne_verticalUnder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:26:07.16281+00:00
-- url     : https://prove2.me/theorems/acada1db-5bd0-4597-8d96-cdf91cfc171f
-- title:
--   Tanner Lifted Product: lps Original Normal Zero height One vertical Under
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normal Zero height One vertical Under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L304-L320
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L304-L320

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeJAlgebra
variable (N : ℕ) (hN : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeBaseFieldAlgebra
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeNormalCommRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeNormalRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.verticalPrimeNormalSemiring
include hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_heightOne_verticalUnder
    (p : ℕ) [Fact p.Prime] (q : Ideal C) [q.IsPrime]
    (hq : q.height = 1) (hpq : (p : C) ∈ q) :
    q.under (Polynomial ℤ) = lpsOriginalGaussPrime p := by sorry
