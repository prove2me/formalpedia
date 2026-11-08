-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactPairFactors_of_weighted
-- name    : QEC.Coding.TannerLiftedProduct.exactPairFactors_of_weighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:21:42.184621+00:00
-- url     : https://prove2.me/theorems/c5d9b506-4130-4107-b665-9cd20d77260f
-- title:
--   Tanner Lifted Product: exact Pair Factors of weighted
-- statement:
--   Four weighted binomial budgets and two coarse rectangle budgets imply the
--   exact six finite inequalities consumed by the simultaneous two-orientation
--   local-pair theorem.  The auxiliary base `L` is free and can later be chosen
--   to optimize the linear exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerPairExistence.lean#L32-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerPairExistence.lean#L32-L73

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

theorem QEC.Coding.TannerLiftedProduct.exactPairFactors_of_weighted
    (w r r' d m s k q L : Nat) (hd : d ≤ w) (hL : 0 < L)
    (hFirstKernel :
      6 * (q + L) ^ w < q ^ r * L ^ (w - d))
    (hFirstImage :
      (6 * q ^ r) * (q + L) ^ w < q ^ w * L ^ (w - d))
    (hSecondKernel :
      6 * (q + L) ^ w < q ^ r' * L ^ (w - d))
    (hSecondImage :
      (6 * q ^ r') * (q + L) ^ w < q ^ w * L ^ (w - d))
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
