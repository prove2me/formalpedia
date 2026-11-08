-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_add_two
-- name    : QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:44:38.398218+00:00
-- url     : https://prove2.me/theorems/d317fa2b-64da-475f-8601-26c676248c5d
-- title:
--   Tanner Lifted Product: cayley Hecke Element add two
-- statement:
--   The Hecke recurrence holds internally in the finite group algebra.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L38-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeTrace.lean#L38-L45

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_add_two
    (label : W → G) (p : ℂ) (n : ℕ) :
    cayleyHeckeElement label p (n + 2) =
      cayleyHeckeElement label p (n + 1) * cayleyGeneratorSum label -
        algebraMap ℂ (MonoidAlgebra ℂ G) p *
          cayleyHeckeElement label p n := by sorry
