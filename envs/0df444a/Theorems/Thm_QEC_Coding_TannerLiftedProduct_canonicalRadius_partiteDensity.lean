-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_canonicalRadius_partiteDensity
-- name    : QEC.Coding.TannerLiftedProduct.canonicalRadius_partiteDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:27.877222+00:00
-- url     : https://prove2.me/theorems/34653644-9efc-4350-b002-72e7fa5bd04b
-- title:
--   Tanner Lifted Product: canonical Radius partite Density
-- statement:
--   The canonical radius has density at most one when normalized by the size
--   of a single bipartite part.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L102-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L102-L110

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
omit [DecidableEq W] [(a : A) → Group (G a)]
    [(a : A) → DecidableEq (G a)]

theorem QEC.Coding.TannerLiftedProduct.canonicalRadius_partiteDensity (a : A) :
    (Fintype.card W : ℝ) * canonicalRadius (W := W) (G := G) a ≤
      (1 : ℝ) * Fintype.card (G a) := by sorry
