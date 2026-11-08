-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_cayleyRightRegularRepresentation_asAlgebraHom
-- name    : QEC.Coding.TannerLiftedProduct.trace_cayleyRightRegularRepresentation_asAlgebraHom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:12:28.609401+00:00
-- url     : https://prove2.me/theorems/2225f4f6-1f09-4744-8176-f42a0b6e79ce
-- title:
--   Tanner Lifted Product: trace cayley Right Regular Representation as Algebra Hom
-- statement:
--   In the finite right regular representation, the trace of a group-algebra
--   element is the group order times its identity coefficient.  This is the
--   generic trace/count bridge used by the LPS Hecke calculation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L172-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L172-L194

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

theorem QEC.Coding.TannerLiftedProduct.trace_cayleyRightRegularRepresentation_asAlgebraHom
    (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ (G → ℂ)
        (cayleyRightRegularRepresentation.asAlgebraHom a) =
      (Fintype.card G : ℂ) * a.coeff 1 := by sorry
