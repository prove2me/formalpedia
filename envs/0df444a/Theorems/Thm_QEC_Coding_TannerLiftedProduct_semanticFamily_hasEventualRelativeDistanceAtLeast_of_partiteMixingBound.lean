-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_semanticFamily_hasEventualRelativeDistanceAtLeast_of_partiteMixingBound
-- name    : QEC.Coding.TannerLiftedProduct.semanticFamily_hasEventualRelativeDistanceAtLeast_of_partiteMixingBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:07.344236+00:00
-- url     : https://prove2.me/theorems/179ae02c-ee54-4e54-b4ed-fe3032827788
-- title:
--   Tanner Lifted Product: semantic Family has Eventual Relative Distance At Least of partite Mixing Bound
-- statement:
--   Source-compatible partite-mixing form of the semantic distance theorem.
--   Unlike a full mean-zero bound on the double cover, this hypothesis permits
--   the unavoidable side-sign trivial eigenmode.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L354-L410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L354-L410

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {A F W R R' : Type u} {G : A → Type u}
variable [Field F] [Fintype F]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
variable [∀ a, Group (G a)] [∀ a, Fintype (G a)]
variable [∀ a, DecidableEq (G a)]
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_34
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_35

theorem QEC.Coding.TannerLiftedProduct.semanticFamily_hasEventualRelativeDistanceAtLeast_of_partiteMixingBound
    (label : ∀ a, W → G a) (h : Matrix R W F) (h' : Matrix R' W F)
    (hW : 0 < Fintype.card W)
    (hGroupCofinal : ∀ N : Nat, ∃ a : A, N ≤ Fintype.card (G a))
    (hRank : h.rank = Fintype.card R)
    (h'Rank : h'.rank = Fintype.card R')
    (d m s : Nat) (beta : ℝ)
    (hProductExpand : ProductExpansion.ProductExpanding h
      (ProductExpansion.generatorImageParityCheck h') s (2 * m) beta)
    (hProductExpandReverse : ProductExpansion.ProductExpanding h'
      (ProductExpansion.generatorImageParityCheck h) s (2 * m) beta)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hDistanceReverse : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h').carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hLength : d ≤ Fintype.card W)
    (hTwo : 2 ≤ Fintype.card W) (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W)
    (spectral : ℝ) (hSpectralNonnegative : 0 ≤ spectral)
    (hMixing : ∀ a, HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph (label a)) (Fintype.card W) spectral)
    (hVerticalThreshold : (2 * m : ℝ) + (spectral + 1) ≤ d)
    (hEdgeThreshold : 2 * (2 * (spectral + 1)) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * (spectral + 1) ^ 2)) ≤ s)
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R')) :
    QEC.QLDPC.HasEventualRelativeDistanceAtLeast
      (semanticFamily label h h' hW hGroupCofinal)
      (canonicalRelativeDistance (W := W) (R := R) (R' := R')) := by sorry
