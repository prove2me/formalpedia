-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalZero_verticalUnramified
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_verticalUnramified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:27:11.627904+00:00
-- url     : https://prove2.me/theorems/5883f9c6-a387-436f-a464-286dd54232f2
-- title:
--   Tanner Lifted Product: lps Original Normal Zero vertical Unramified
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normal Zero vertical Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalVerticalUnramified.lean#L108-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalVerticalUnramified.lean#L108-L138

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.Locus
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalVerticalUnramified
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring verticalPrimeJAlgebra
  verticalPrimeBaseFieldAlgebra verticalPrimeNormalCommRing verticalPrimeNormalRing
  verticalPrimeNormalSemiring
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
local notation "D" => integralClosure (LPSOriginalGaussBase p) K
include hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_verticalUnramified
    (hpN : ¬ p ∣ N) (q : Ideal C) [q.IsPrime] (hq : q.height = 1)
    (hpq : (p : C) ∈ q) : Algebra.IsUnramifiedAt (Polynomial ℤ) q := by sorry
