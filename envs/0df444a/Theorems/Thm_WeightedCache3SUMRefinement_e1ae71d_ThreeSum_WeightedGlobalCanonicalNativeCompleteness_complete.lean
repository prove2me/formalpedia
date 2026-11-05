-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCanonicalNativeCompleteness_complete
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalNativeCompleteness.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:45:56.211092+00:00
-- url     : https://prove2.me/theorems/7737c7db-d934-4905-a469-3fed3a204033
-- title:
--   complete
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCanonicalNativeCompleteness.lean#L27-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCanonicalNativeCompleteness.lean#L27-L97

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Theorems.Thm_ThreeSum_TernaryNearCanonical_complete

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalNativeCompleteness
open Finset TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalCoverGoodMaps
open WeightedGlobalNativeCoverWitness TernaryExtensionEncoding TernaryFixedDictionaries
open TernaryCanonicalDictionaries LightTernarySourceHost WeightedGlobalRepeatedWords
set_option maxHeartbeats 4000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCanonicalNativeCompleteness.complete (maps : Fin F→Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, WeightedGlobalCoverFrequency.Covers m p B τ (maps i) (a,b))
    (a b : Fin r→ZMod p) :
    ∃ occ : Fin r→Fin F, ∃ e : Fin r→ActualEdge m, ∃ jL jR : ℕ,
      jL<(records (α := fixedAlpha m) false maps B).length^r ∧
      jR<(records (α := fixedAlpha m) true maps B).length^r ∧
      dictionary ((records (α := fixedAlpha m) false maps B).map (native false maps)) p r jL=(coefficientCode a : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) true maps B).map (native true maps)) p r jR=(coefficientCode b : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) false maps B).map wordCode) (4^(fixedLength m)) r jL=
        (TernaryCodeSemantics.address (canonical (fun i => left (e i))) : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) true maps B).map wordCode) (4^(fixedLength m)) r jR=
        (TernaryCodeSemantics.address (canonical (fun i => right (e i))) : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) false maps B).map mapCode) F r jL=(bankId occ : ℤ) ∧
      dictionary ((records (α := fixedAlpha m) true maps B).map mapCode) F r jR=(bankId occ : ℤ) ∧
      (TernaryCodeSemantics.address (canonical (fun i => output (e i))),bankId occ)∈
        TernaryWantedLittleEndian.wantedCodes (p : ℤ)
          (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
          (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) r (coefficientCode (a+b) : ℤ)
          (4^(fixedLength m)) F 0 1 0 1 ∧
      TernaryConvolution.Adds (canonical (fun i => left (e i)))
        (canonical (fun i => right (e i))) (canonical (fun i => output (e i))) := by sorry
