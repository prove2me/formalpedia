-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_logarithmicRows_blockWitnesses
-- name    : QEC.Coding.TannerLiftedProduct.logarithmicRows_blockWitnesses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:13:21.386834+00:00
-- url     : https://prove2.me/theorems/cf43b1b4-528f-44f4-ad0c-53d8e0b02121
-- title:
--   Tanner Lifted Product: logarithmic Rows block Witnesses
-- statement:
--   Choosing the same logarithmic row count in both orientations gives all
--   four one-block weighted inequalities once twice that row count fits in the
--   local length.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L117-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L117-L135

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_25

theorem QEC.Coding.TannerLiftedProduct.logarithmicRows_blockWitnesses
    (q A D : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hD : D ≤ A)
    (hRowsFit : 2 * logarithmicLocalRows q A D ≤ A) :
    let B := logarithmicLocalRows q A D
    let L := quadraticWeightBase q A
    (6 * (q + L) ^ A < q ^ B * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ B * L ^ (A - D)) ∧
    (6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D)) := by sorry
