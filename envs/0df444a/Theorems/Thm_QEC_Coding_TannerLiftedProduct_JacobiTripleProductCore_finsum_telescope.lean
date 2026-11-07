-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finsum_telescope
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finsum_telescope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:31.336498+00:00
-- url     : https://prove2.me/theorems/07edf688-5793-4977-8036-44f55d011df0
-- title:
--   Jacobi Triple Product Core: finsum telescope
-- statement:
--   The Jacobi Triple Product Core construction uses the finsum telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1694-L1712
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1694-L1712

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finsum_telescope {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (ht : (Function.support t).Finite)
    (hw : (Function.support w).Finite)
    (hu : (Function.support u).Finite)
    (h_zero : t 0 = w 0)
    (h_succ : ∀ ℓ, t (ℓ + 1) = w (ℓ + 1) - u ℓ) :
    ∑ᶠ ℓ, t ℓ = ∑ᶠ ℓ, w ℓ - ∑ᶠ ℓ, u ℓ := by sorry
