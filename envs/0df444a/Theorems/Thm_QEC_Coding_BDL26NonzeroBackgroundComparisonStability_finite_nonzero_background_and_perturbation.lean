-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_finite_nonzero_background_and_perturbation
-- name    : QEC.Coding.BDL26NonzeroBackgroundComparisonStability.finite_nonzero_background_and_perturbation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:19:09.722216+00:00
-- url     : https://prove2.me/theorems/04de4635-22a8-4e3b-b80d-96831cf06074
-- title:
--   BDL26 Nonzero Background Comparison Stability: finite nonzero background and perturbation
-- statement:
--   Genuine finite consumer: nonzero complete baseline readout AND nonzero perturbation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L403-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L403-L419

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NonzeroBackgroundComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual (suffix_delta0 suffix_delta1)
open BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators

theorem QEC.Coding.BDL26NonzeroBackgroundComparisonStability.finite_nonzero_background_and_perturbation :
    BDL26AllDepthBottomComparisonStability.baseReadout scaleSixtyOne 0 finiteBackgroundInput≠0 ∧
      finiteBackground≠0 ∧
      BDL26AllDepthBottomComparisonStability.SingleFlipStable scaleSixtyOne 0 finiteBackgroundInput ∧
      (Data scaleSixtyOne 0).family.coboundary0 (TopIndex 0) finiteTopPotential=
        BDL26AllDepthBottomComparisonStability.residual scaleSixtyOne 0 finiteBackgroundInput finiteBackground := by sorry
