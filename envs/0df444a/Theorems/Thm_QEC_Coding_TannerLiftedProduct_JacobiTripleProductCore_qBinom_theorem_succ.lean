-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_theorem_succ
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_theorem_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:40.746334+00:00
-- url     : https://prove2.me/theorems/6e5910f1-74ee-4c67-83a5-a2a655410d6b
-- title:
--   Jacobi Triple Product Core: q Binom theorem succ
-- statement:
--   The Jacobi Triple Product Core construction uses the q Binom theorem succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L175-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L175-L187

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_theorem_succ (A Q : R) (n : ℕ)
    (ih : ∀ (A' : R), qPoch A' Q n =
      ∑ k ∈ Finset.range (n + 1), qBinom Q n k * (-A') ^ k * Q ^ k.choose 2) :
    qPoch A Q (n + 1) =
    ∑ k ∈ Finset.range (n + 2), qBinom Q (n + 1) k * (-A) ^ k * Q ^ k.choose 2 := by sorry
