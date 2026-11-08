-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyCenteredGeneratorSum_action
-- name    : QEC.Coding.TannerLiftedProduct.cayleyCenteredGeneratorSum_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:12:07.983199+00:00
-- url     : https://prove2.me/theorems/6790e47e-e2f3-45e4-a9c1-eb7e013465bb
-- title:
--   Tanner Lifted Product: cayley Centered Generator Sum action
-- statement:
--   Acting by the centered generator sum is adjacency with the constant mode
--   subtracted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L208-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L208-L216

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.cayleyCenteredGeneratorSum_action
    (label : W → G) (f : G → ℂ) (g : G) :
    (cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyCenteredGeneratorSum label) f) g =
      cayleyRightTranslationSum label f g -
        ((Fintype.card W : ℂ) / (Fintype.card G : ℂ)) * ∑ h, f h := by sorry
