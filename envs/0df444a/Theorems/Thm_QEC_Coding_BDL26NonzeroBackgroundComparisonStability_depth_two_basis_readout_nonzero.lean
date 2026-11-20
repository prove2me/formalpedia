-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_depth_two_basis_readout_nonzero
-- name    : QEC.Coding.BDL26NonzeroBackgroundComparisonStability.depth_two_basis_readout_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:18:12.754502+00:00
-- url     : https://prove2.me/theorems/3937f127-0477-4f83-9b6e-c91d54daf33d
-- title:
--   BDL26 Nonzero Background Comparison Stability: depth two basis readout nonzero
-- statement:
--   The new first bottom readout can be genuinely nonzero, not merely permitted syntactically.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L357-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L357-L374

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

theorem QEC.Coding.BDL26NonzeroBackgroundComparisonStability.depth_two_basis_readout_nonzero (S : OddScale) (q : TopQ S 0) :
    BDL26AllDepthBottomComparisonStability.baseReadout S 0
      (perturbTop S 0 (zeroInput S 0) (canonicalBasisWord (F:=F) q))≠0 := by sorry
