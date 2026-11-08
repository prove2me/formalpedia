-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_polynomialScheduled_localPair
-- name    : QEC.Coding.TannerLiftedProduct.exists_polynomialScheduled_localPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:12:28.327385+00:00
-- url     : https://prove2.me/theorems/c79b79fe-09cb-4b7c-b7ef-207480e122f3
-- title:
--   Tanner Lifted Product: exists polynomial Scheduled local Pair
-- statement:
--   The coefficient-bearing polynomial schedule constructs one simultaneous
--   random local-code pair, independently of the eventual labelled graph family.
--   All probabilistic estimates are discharged by finite block witnesses and
--   integer coefficient inequalities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L541-L630
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L541-L630

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

theorem QEC.Coding.TannerLiftedProduct.exists_polynomialScheduled_localPair
    (A D M S K B B' L n : Nat)
    (hWCard : Fintype.card W = A * n ^ 6)
    (hRCard : Fintype.card R = B * n ^ 6)
    (hR'Card : Fintype.card R' = B' * n ^ 6)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hA : 0 < A) (hDPositive : 0 < D) (hL : 0 < L) (hn : 0 < n)
    (hSmall : 12 * M ≤ D * n ^ 2)
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
      2 * A + 2 * A * S + 4 * M * A + 16 * S + 11 < K * B * n)
    (hReverseThreshold :
      2 * A + 2 * A * S + 4 * M * A + 16 * S + 11 < K * B' * n) :
    ∃ (h : Matrix R W F) (h' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      h'.rank = Fintype.card R' ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h).carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h)).carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h').carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h')).carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h')
        (S * n ^ 7) (2 * (M * n ^ 4))
        (((D * n ^ 6 : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) ∧
      ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h)
        (S * n ^ 7) (2 * (M * n ^ 4))
        (((D * n ^ 6 : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) := by sorry
