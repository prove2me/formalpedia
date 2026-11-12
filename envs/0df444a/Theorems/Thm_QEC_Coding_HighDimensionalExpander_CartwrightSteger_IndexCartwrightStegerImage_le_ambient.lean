-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_IndexCartwrightStegerImage_le_ambient
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexCartwrightStegerImage_le_ambient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:56:59.07589+00:00
-- url     : https://prove2.me/theorems/5352a15a-b917-4763-b44b-2e55dee2b8ba
-- title:
--   Cartwright Steger: Index Cartwright Steger Image le ambient
-- statement:
--   The actual Cartwright--Steger image is contained in its explicit ambient
--   group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L131-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/IntrinsicStrongApproximation.lean#L131-L137

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_NormOneCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped PowerSeries.WithPiTopology
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.intrinsicResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexCartwrightStegerImage_le_ambient
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexCartwrightStegerImage P r level ≤
      IndexCartwrightStegerAmbient P r level := by sorry
