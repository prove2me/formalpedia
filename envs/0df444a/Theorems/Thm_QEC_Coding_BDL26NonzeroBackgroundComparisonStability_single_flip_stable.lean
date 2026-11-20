-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_single_flip_stable
-- name    : QEC.Coding.BDL26NonzeroBackgroundComparisonStability.single_flip_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:17:10.757661+00:00
-- url     : https://prove2.me/theorems/8898c609-8b62-4d13-9cb8-a0d0f7849cd0
-- title:
--   BDL26 Nonzero Background Comparison Stability: single flip stable
-- statement:
--   Actual single-coordinate perturbations need no supplied star centre or support certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L312-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L312-L319

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

theorem QEC.Coding.BDL26NonzeroBackgroundComparisonStability.single_flip_stable (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.SingleFlipStable S n (perturbTop S n sigma0 g) := by sorry
