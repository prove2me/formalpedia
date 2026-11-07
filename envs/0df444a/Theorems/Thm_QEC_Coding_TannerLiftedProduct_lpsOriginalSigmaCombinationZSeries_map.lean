-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalSigmaCombinationZSeries_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalSigmaCombinationZSeries_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:23.425251+00:00
-- url     : https://prove2.me/theorems/2fcd58da-2731-4b04-b289-f29101e0dea0
-- title:
--   Tanner Lifted Product: lps Original Sigma Combination ZSeries map
-- statement:
--   The faithful rational map of that exact integer combination equals the actual divided sigma combination.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L90-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerQExpansion.lean#L90-L101

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalSigmaCombinationZSeries_map :
    PowerSeries.map (algebraMap ℤ ℚ) lpsOriginalSigmaCombinationZSeries=
      PowerSeries.C (12:ℚ)⁻¹*
        (PowerSeries.C (5:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 3)+
          PowerSeries.C (7:ℚ)*PowerSeries.map (algebraMap ℤ ℚ) (lpsOriginalSigmaZSeries 5)) := by sorry
