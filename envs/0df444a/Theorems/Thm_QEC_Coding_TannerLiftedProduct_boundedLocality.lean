-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundedLocality
-- name    : QEC.Coding.TannerLiftedProduct.boundedLocality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:13:29.622976+00:00
-- url     : https://prove2.me/theorems/9b8e9657-a33f-4787-804f-5d54a002f3df
-- title:
--   Tanner Lifted Product: bounded Locality
-- statement:
--   The Tanner lifted-product incidence is uniformly local. Its explicit
--   bound depends only on the three local matrix dimensions, not on `|G|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L548-L558
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L548-L558

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.LiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.boundedLocality
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    QEC.Coding.BoundedLocality
      (LiftedProduct.boundaryIncidence (data label h g')).localityProfile
      (2 * (Fintype.card W + Fintype.card R + Fintype.card R')) := by sorry
