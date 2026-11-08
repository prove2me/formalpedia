-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactPairFactors_of_coarse
-- name    : QEC.Coding.TannerLiftedProduct.exactPairFactors_of_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:21:59.269171+00:00
-- url     : https://prove2.me/theorems/1a2774b7-9481-4369-b023-59df84339f6c
-- title:
--   Tanner Lifted Product: exact Pair Factors of coarse
-- statement:
--   Six coarse power inequalities imply the exact six finite inequalities
--   consumed by the simultaneous two-orientation local-pair theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerPairExistence.lean#L77-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerPairExistence.lean#L77-L115

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

theorem QEC.Coding.TannerLiftedProduct.exactPairFactors_of_coarse
    (w r r' d m s k q : Nat) (hq : 0 < q)
    (hFirstKernel : 6 * coarseLowWeightFactor w d q < q ^ r)
    (hFirstImage :
      6 * (q ^ r * coarseLowWeightFactor w d q) < q ^ w)
    (hSecondKernel : 6 * coarseLowWeightFactor w d q < q ^ r')
    (hSecondImage :
      6 * (q ^ r' * coarseLowWeightFactor w d q) < q ^ w)
    (hForwardRectangle :
      6 * coarseRectangleFactor w m s q < q ^ (k * r))
    (hReverseRectangle :
      6 * coarseRectangleFactor w m s q < q ^ (k * r')) :
    (6 * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < q ^ r) ∧
    (6 * (q ^ r *
      (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1)) < q ^ w) ∧
    (6 * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < q ^ r') ∧
    (6 * (q ^ r' *
      (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1)) < q ^ w) ∧
    (6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ (k * r)) ∧
    (6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ (k * r')) := by sorry
