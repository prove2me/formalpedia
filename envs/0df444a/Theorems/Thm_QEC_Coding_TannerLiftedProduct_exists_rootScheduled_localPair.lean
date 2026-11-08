-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_rootScheduled_localPair
-- name    : QEC.Coding.TannerLiftedProduct.exists_rootScheduled_localPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:18:26.598948+00:00
-- url     : https://prove2.me/theorems/00fa256a-6b9f-4e30-87d3-9bb9584d6252
-- title:
--   Tanner Lifted Product: exists root Scheduled local Pair
-- statement:
--   Construct the simultaneous random local-code pair at every compatible
--   replication count `N`, using `x = floor(N^(1/6))` only for the auxiliary
--   sublinear scales.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L637-L732
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L637-L732

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
omit [DecidableEq R] [DecidableEq R']
set_option maxHeartbeats 1200000

theorem QEC.Coding.TannerLiftedProduct.exists_rootScheduled_localPair
    (A D M S K B B' L N x : Nat)
    (hWCard : Fintype.card W = A * N)
    (hRCard : Fintype.card R = B * N)
    (hR'Card : Fintype.card R' = B' * N)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hA : 0 < A) (hDPositive : 0 < D) (hL : 0 < L) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hSmall : 12 * M ≤ D * x ^ 2)
    (hRankTarget : 36 * K * S ≤ 5 * D ^ 2)
    (hFirstKernelBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ (A - B') * L ^ (A - D))
    (hForwardThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B * x)
    (hReverseThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B' * x) :
    ∃ (h : Matrix R W F) (h' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      h'.rank = Fintype.card R' ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h).carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h)).carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h').carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h')).carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h')
        (S * x ^ 7) (2 * (M * x ^ 4))
        (((D * N : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) ∧
      ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h)
        (S * x ^ 7) (2 * (M * x ^ 4))
        (((D * N : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) := by sorry
