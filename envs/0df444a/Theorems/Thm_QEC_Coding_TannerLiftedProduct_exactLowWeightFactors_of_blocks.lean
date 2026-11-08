-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactLowWeightFactors_of_blocks
-- name    : QEC.Coding.TannerLiftedProduct.exactLowWeightFactors_of_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:26.480423+00:00
-- url     : https://prove2.me/theorems/9fb4909c-d8cc-4c7b-bf4e-86a20befed1a
-- title:
--   Tanner Lifted Product: exact Low Weight Factors of blocks
-- statement:
--   Two one-block weighted budgets for each local dimension produce all four
--   exact low-weight bad-event inequalities on every positive block multiple.
--   The complementary exponents `A - B` and `A - B'` are precisely the image
--   budgets after multiplying by the respective rank powers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L223-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L223-L292

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

theorem QEC.Coding.TannerLiftedProduct.exactLowWeightFactors_of_blocks
    (A D B B' q L n : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 0 < q) (hL : 0 < L) (hn : 0 < n)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D)) :
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B * n)) ∧
    (6 * (q ^ (B * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) ∧
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B' * n)) ∧
    (6 * (q ^ (B' * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) := by sorry
