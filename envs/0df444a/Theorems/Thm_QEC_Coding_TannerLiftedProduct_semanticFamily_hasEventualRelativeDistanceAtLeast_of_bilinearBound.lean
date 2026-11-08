-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_semanticFamily_hasEventualRelativeDistanceAtLeast_of_bilinearBound
-- name    : QEC.Coding.TannerLiftedProduct.semanticFamily_hasEventualRelativeDistanceAtLeast_of_bilinearBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:08.376949+00:00
-- url     : https://prove2.me/theorems/9f701637-c902-4fa0-b235-2e64597394a3
-- title:
--   Tanner Lifted Product: semantic Family has Eventual Relative Distance At Least of bilinear Bound
-- statement:
--   A uniform two-sided spectral bound on the labelled double covers gives a
--   fully concrete eventual relative-distance bound.  Both the graph radius and
--   the positive relative-distance constant are the canonical definitions above;
--   neither is supplied as conclusion-bearing data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L293-L349
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L293-L349

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

theorem QEC.Coding.TannerLiftedProduct.semanticFamily_hasEventualRelativeDistanceAtLeast_of_bilinearBound
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
    (hSpectral : ∀ a, SmallSetExpansion.HasMeanZeroBilinearBound
      (rightDoubleCoverGraph (label a)) spectral)
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
