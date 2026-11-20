-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_source_scale_single_flip_stable
-- name    : QEC.Coding.BDL26NonzeroBackgroundComparisonStability.source_scale_single_flip_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T15:10:00.027359+00:00
-- url     : https://prove2.me/theorems/8c63e99e-5afc-4327-ae12-46b886c88a7c
-- title:
--   BDL26 Nonzero Background Comparison Stability: source scale single flip stable
-- statement:
--   The BDL26 Nonzero Background Comparison Stability construction uses the source scale single flip stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L327-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/NonzeroBackgroundComparisonStability.lean#L327-L332

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_source_scale_single_flip_stable
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

theorem QEC.Coding.BDL26NonzeroBackgroundComparisonStability.source_scale_single_flip_stable (S : OddScale) (n : Nat) (B : Nat)
    (large : 28*B+33 ≤ S.ell) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) :
    BDL26AllDepthBottomComparisonStability.SingleFlipStable S n (perturbTop S n sigma0 g) := by sorry
