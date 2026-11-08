-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_canonicalRadius_density
-- name    : QEC.Coding.TannerLiftedProduct.canonicalRadius_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:29:37.152259+00:00
-- url     : https://prove2.me/theorems/e6fcef79-31f8-416e-8723-ec9da64eadb2
-- title:
--   Tanner Lifted Product: canonical Radius density
-- statement:
--   The canonical radius makes the uniform-density contribution at most one
--   in the division-free expander-mixing estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L88-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L88-L96

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

theorem QEC.Coding.TannerLiftedProduct.canonicalRadius_density (a : A) :
    (Fintype.card W : ℝ) * canonicalRadius (W := W) (G := G) a ≤
      (1 : ℝ) * Fintype.card (Fin 2 × G a) := by sorry
