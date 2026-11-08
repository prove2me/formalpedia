-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactPairFactors_of_polynomialSchedule
-- name    : QEC.Coding.TannerLiftedProduct.exactPairFactors_of_polynomialSchedule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:11:03.434466+00:00
-- url     : https://prove2.me/theorems/c11bfa39-4e4f-4241-8ee4-5fd8dd4c7def
-- title:
--   Tanner Lifted Product: exact Pair Factors of polynomial Schedule
-- statement:
--   The concrete polynomial schedule
--   `w = A n^6`, `d = D n^6`, `m = n^4`, `s = n^7`, `k = n^5`
--   discharges all six exact pair inequalities from four finite block witnesses
--   and two linear lower bounds on `n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L444-L484
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L444-L484

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

theorem QEC.Coding.TannerLiftedProduct.exactPairFactors_of_polynomialSchedule
    (A D B B' q L n : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 2 ≤ q) (hA : 0 < A) (hL : 0 < L) (hn : 0 < n)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D))
    (hForwardThreshold : 8 * A + 26 < B * n)
    (hReverseThreshold : 8 * A + 26 < B' * n) :
    (6 * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1) < q ^ (B * n ^ 6)) ∧
    (6 * (q ^ (B * n ^ 6) * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1)) < q ^ (A * n ^ 6)) ∧
    (6 * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1) < q ^ (B' * n ^ 6)) ∧
    (6 * (q ^ (B' * n ^ 6) * (∑ t : Fin (D * n ^ 6),
      Nat.choose (A * n ^ 6) t.1 * q ^ t.1)) < q ^ (A * n ^ 6)) ∧
    (6 * ((Nat.choose (A * n ^ 6) (A * n ^ 6 - 2 * n ^ 4)) ^ 2 *
      (n ^ 7 * (((A * n ^ 6 - 2 * n ^ 4) *
        (A * n ^ 6 - 2 * n ^ 4) + 1) ^ (n ^ 7)) *
        q ^ (2 * (2 * n ^ 4) * (A * n ^ 6) + n ^ 7))) <
          q ^ (n ^ 5 * (B * n ^ 6))) ∧
    (6 * ((Nat.choose (A * n ^ 6) (A * n ^ 6 - 2 * n ^ 4)) ^ 2 *
      (n ^ 7 * (((A * n ^ 6 - 2 * n ^ 4) *
        (A * n ^ 6 - 2 * n ^ 4) + 1) ^ (n ^ 7)) *
        q ^ (2 * (2 * n ^ 4) * (A * n ^ 6) + n ^ 7))) <
          q ^ (n ^ 5 * (B' * n ^ 6))) := by sorry
