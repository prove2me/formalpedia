-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJLineToSpecZ_quasiSeparated
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLineToSpecZ_quasiSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:02:52.293107+00:00
-- url     : https://prove2.me/theorems/2f52362e-65b4-4649-a4fa-f9c3aae382fa
-- title:
--   Tanner Lifted Product: lps Original Integer Projective JLine To Spec Z quasi Separated
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Projective JLine To Spec Z quasi Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L929-L932
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean#L929-L932

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLineToSpecZ_quasiSeparated :
    QuasiSeparated lpsOriginalIntegerProjectiveJLineToSpecZ := by sorry
