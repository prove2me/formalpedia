-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyGroupSum_action
-- name    : QEC.Coding.TannerLiftedProduct.cayleyGroupSum_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:12:00.47618+00:00
-- url     : https://prove2.me/theorems/ffba6272-ba1c-4063-951b-5d1859dadf3d
-- title:
--   Tanner Lifted Product: cayley Group Sum action
-- statement:
--   The full group sum acts in the right regular representation by the
--   constant function whose value is the sum of the input coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L81-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L81-L88

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

theorem QEC.Coding.TannerLiftedProduct.cayleyGroupSum_action (f : G → ℂ) (g : G) :
    (cayleyRightRegularRepresentation.asAlgebraHom cayleyGroupSum f) g =
      ∑ h, f h := by sorry
