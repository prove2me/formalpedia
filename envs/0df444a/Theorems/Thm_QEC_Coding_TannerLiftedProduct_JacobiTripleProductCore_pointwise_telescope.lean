-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_pointwise_telescope
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.pointwise_telescope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:36.603929+00:00
-- url     : https://prove2.me/theorems/97ca1998-83b9-47a6-a3a7-e3c0884cfc44
-- title:
--   Jacobi Triple Product Core: pointwise telescope
-- statement:
--   The Jacobi Triple Product Core construction uses the pointwise telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1567-L1574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1567-L1574

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.pointwise_telescope (j ℓ : ℕ) :
    (-A_hahn j) ^ (ℓ + 1) * Q₀ ^ ((ℓ + 1).choose 2) * V (ℓ + 1) =
    (-(A_hahn j * Q₀)) ^ (ℓ + 1) * Q₀ ^ ((ℓ + 1).choose 2) * V (ℓ + 1) -
    A_hahn j * ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ) := by sorry
