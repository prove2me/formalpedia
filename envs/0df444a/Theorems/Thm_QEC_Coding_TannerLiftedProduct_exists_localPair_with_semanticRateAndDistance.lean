-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_localPair_with_semanticRateAndDistance
-- name    : QEC.Coding.TannerLiftedProduct.exists_localPair_with_semanticRateAndDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:22:00.030048+00:00
-- url     : https://prove2.me/theorems/36d6bef0-30a6-4d12-906a-a5ed16d12c92
-- title:
--   Tanner Lifted Product: exists local Pair with semantic Rate And Distance
-- statement:
--   The simultaneous random local-code package, together with one expanding
--   labelled double cover, produces Tanner lifted products whose attained
--   algebraic CSS distance is at least the graph radius divided by `2 |W|`.
--
--   The theorem deliberately leaves the local dimensions and numerical
--   inequalities explicit.  Choosing them uniformly and supplying a cofinal graph
--   family is the final asymptotic construction step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerPairExistence.lean#L125-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerPairExistence.lean#L125-L223

import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_62dc6baf31_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_62dc6baf31_24
set_option maxHeartbeats 1200000

theorem QEC.Coding.TannerLiftedProduct.exists_localPair_with_semanticRateAndDistance
    (label : W → G)
    (d s m k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * (2 * m) ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hFirstKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hFirstImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hSecondKernelFactor :
      6 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R')
    (hSecondImageFactor :
      6 * ((Nat.card F) ^ Fintype.card R' *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) <
        (Nat.card F) ^ Fintype.card W)
    (hForwardRectangleFactor :
      6 * ((Nat.choose (Fintype.card W)
          (Fintype.card W - 2 * m)) ^ 2 *
        (s * (((Fintype.card W - 2 * m) *
          (Fintype.card W - 2 * m) + 1) ^ s) *
          (Nat.card F) ^ (2 * (2 * m) * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R))
    (hReverseRectangleFactor :
      6 * ((Nat.choose (Fintype.card W)
          (Fintype.card W - 2 * m)) ^ 2 *
        (s * (((Fintype.card W - 2 * m) *
          (Fintype.card W - 2 * m) + 1) ^ s) *
          (Nat.card F) ^ (2 * (2 * m) * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R'))
    (rate : ℝ) (hRatePositive : 0 < rate)
    (hRatio :
      2 * ((Fintype.card R : ℝ) + Fintype.card R') * Fintype.card W ≤
        (1 - rate) *
          ((Fintype.card W : ℝ) ^ 2 +
            4 * Fintype.card R * Fintype.card R'))
    (hFour : 4 ≤ d)
    (hDistanceScale : 4 * m ≤ d)
    (hRectangleScale : 4 * s ≤ m * d)
    (hBudget : 4 * (m : ℝ) + 2 ≤
      ((d : ℝ) / (3 * (Fintype.card W : ℝ))) * Fintype.card W)
    (radius : Nat) (lambda : ℝ) (hLambda : 0 < lambda)
    (hBase : SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius lambda)
    (hVerticalThreshold : (2 * m : ℝ) + lambda ≤ d)
    (hEdgeThreshold : 2 * (2 * lambda) ≤ m)
    (hFaceThreshold :
      2 * (((Nat.log 2 (2 * Fintype.card W) + 1 : Nat) : ℝ) *
        (8 * lambda ^ 2)) ≤ s) :
    ∃ (h : Matrix R W F) (h' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      h'.rank = Fintype.card R' ∧
      rate * ((semanticPresentation label h h').blockLength : ℝ) ≤
        ((semanticPresentation label h h').encodedQudits : ℝ) ∧
      radius / (2 * Fintype.card W) + 1 ≤
        (semanticPresentation label h h').distance := by sorry
