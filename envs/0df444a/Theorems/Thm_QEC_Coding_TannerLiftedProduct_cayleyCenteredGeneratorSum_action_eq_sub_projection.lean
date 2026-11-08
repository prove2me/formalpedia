-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyCenteredGeneratorSum_action_eq_sub_projection
-- name    : QEC.Coding.TannerLiftedProduct.cayleyCenteredGeneratorSum_action_eq_sub_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:12:03.919907+00:00
-- url     : https://prove2.me/theorems/2a1303e3-63f0-405a-878c-4b7fcd23f5fa
-- title:
--   Tanner Lifted Product: cayley Centered Generator Sum action eq sub projection
-- statement:
--   The centered right-regular adjacency is ordinary adjacency minus the
--   degree times the rank-one constant projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L220-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L220-L233

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

theorem QEC.Coding.TannerLiftedProduct.cayleyCenteredGeneratorSum_action_eq_sub_projection
    (label : W → G) :
    cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyCenteredGeneratorSum label) =
      cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyGeneratorSum label) -
        (Fintype.card W : ℂ) • cayleyConstantProjection := by sorry
