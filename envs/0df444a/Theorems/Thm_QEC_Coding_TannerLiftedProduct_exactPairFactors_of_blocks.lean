-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactPairFactors_of_blocks
-- name    : QEC.Coding.TannerLiftedProduct.exactPairFactors_of_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:47.389581+00:00
-- url     : https://prove2.me/theorems/cbc1f979-e8d8-47b9-814c-ecb9572fed1f
-- title:
--   Tanner Lifted Product: exact Pair Factors of blocks
-- statement:
--   Finite block witnesses for the low-weight terms and two integer exponent
--   comparisons for the rectangle terms imply all six exact pair inequalities.
--   This is the arithmetic endpoint needed by the random local-pair theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L400-L438
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L400-L438

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

theorem QEC.Coding.TannerLiftedProduct.exactPairFactors_of_blocks
    (A D B B' m s k q L n : Nat)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hq : 2 ≤ q) (hL : 0 < L) (hn : 0 < n)
    (hFirstKernelBlock :
      6 * (q + L) ^ A < q ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (q + L) ^ A < q ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (q + L) ^ A < q ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (q + L) ^ A < q ^ (A - B') * L ^ (A - D))
    (hForwardRectangle :
      coarseRectangleExponent (A * n) m s q + 3 < k * (B * n))
    (hReverseRectangle :
      coarseRectangleExponent (A * n) m s q + 3 < k * (B' * n)) :
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B * n)) ∧
    (6 * (q ^ (B * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) ∧
    (6 * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1) < q ^ (B' * n)) ∧
    (6 * (q ^ (B' * n) * (∑ t : Fin (D * n),
      Nat.choose (A * n) t.1 * q ^ t.1)) < q ^ (A * n)) ∧
    (6 * ((Nat.choose (A * n) (A * n - 2 * m)) ^ 2 *
      (s * (((A * n - 2 * m) * (A * n - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * (A * n) + s))) < q ^ (k * (B * n))) ∧
    (6 * ((Nat.choose (A * n) (A * n - 2 * m)) ^ 2 *
      (s * (((A * n - 2 * m) * (A * n - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * (A * n) + s))) < q ^ (k * (B' * n))) := by sorry
