-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_telescope_rewrite
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.telescope_rewrite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:17.198434+00:00
-- url     : https://prove2.me/theorems/64786f82-f2c9-4cc2-9347-d12b190ca616
-- title:
--   Jacobi Triple Product Core: telescope rewrite
-- statement:
--   The Jacobi Triple Product Core construction uses the telescope rewrite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1646-L1658
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1646-L1658

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.telescope_rewrite {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (N_val : ℕ)
    (h_zero : t 0 = w 0)
    (h_succ : ∀ ℓ, t (ℓ + 1) = w (ℓ + 1) - u ℓ) :
    ∑ i ∈ Finset.range (N_val + 1), t i =
    ∑ i ∈ Finset.range (N_val + 1), w i - ∑ i ∈ Finset.range N_val, u i := by sorry
