-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finset_range_telescope
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finset_range_telescope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:32.686523+00:00
-- url     : https://prove2.me/theorems/061605a7-1e9f-436b-a60e-1e1a08ac3a96
-- title:
--   Jacobi Triple Product Core: finset range telescope
-- statement:
--   The Jacobi Triple Product Core construction uses the finset range telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1660-L1674
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1660-L1674

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finset_range_telescope {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (N_val : ℕ)
    (ht_van : t (N_val + 1) = 0)
    (hw_van : w (N_val + 1) = 0)
    (h_zero : t 0 = w 0)
    (h_succ : ∀ ℓ, t (ℓ + 1) = w (ℓ + 1) - u ℓ) :
    ∑ i ∈ Finset.range (N_val + 1), t i =
    ∑ i ∈ Finset.range (N_val + 1), w i - ∑ i ∈ Finset.range (N_val + 1), u i := by sorry
