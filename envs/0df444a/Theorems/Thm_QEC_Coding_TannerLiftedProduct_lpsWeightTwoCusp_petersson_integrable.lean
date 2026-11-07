-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_petersson_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_petersson_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:06:14.767948+00:00
-- url     : https://prove2.me/theorems/3114d3b5-d931-4a09-9ce5-42a203b950dd
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp petersson integrable
-- statement:
--   The actual cusp/modular Petersson integrand is integrable on the fundamental domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonMeasure.lean#L64-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonMeasure.lean#L64-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_petersson_integrable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (petersson 2 f g) ModularGroup.fd := by sorry
