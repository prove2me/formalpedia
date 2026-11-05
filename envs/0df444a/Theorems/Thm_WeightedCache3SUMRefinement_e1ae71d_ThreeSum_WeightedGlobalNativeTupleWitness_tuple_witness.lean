-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeTupleWitness_tuple_witness
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTupleWitness.tuple_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:34:15.287169+00:00
-- url     : https://prove2.me/theorems/eae285d1-8c84-4b4b-b1ae-afbcf406ec8f
-- title:
--   tuple_witness
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L55-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L55-L101

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTupleWitness
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTupleWitness
open Finset TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalCoverGoodMaps
open WeightedGlobalNativeCoverWitness TernaryExtensionEncoding TernaryFixedDictionaries
open scoped BigOperators
variable {p m : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTupleWitness.tuple_witness (maps : I → Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, WeightedGlobalCoverFrequency.Covers m p B τ (maps i) (a,b))
    {r : ℕ} (a b : Fin r → ZMod p) :
    ∃ occurrence : Fin r → I, ∃ edge : Fin r → ActualEdge m,
      (List.ofFn fun i => leftRecord (occurrence i) (edge i))∈
        RadixKeyLists.tuples (TernaryCanonicalDictionaries.records false maps B) r ∧
      (List.ofFn fun i => rightRecord (occurrence i) (edge i))∈
        RadixKeyLists.tuples (TernaryCanonicalDictionaries.records true maps B) r ∧
      (List.ofFn fun i => (occurrence i, (⟨output (edge i),output_mem_vertices (edge i)⟩ :
        WeightedGlobalGoodOutputCatalog.Output m)))∈
        RadixKeyLists.tuples (WeightedGlobalGoodOutputCatalog.records maps τ) r ∧
      Radix.positionalHash (p : ℤ) (TernaryCanonicalDictionaries.native false maps)
        (List.ofFn fun i => leftRecord (occurrence i) (edge i))=(coefficientCode a : ℤ) ∧
      Radix.positionalHash (p : ℤ) (TernaryCanonicalDictionaries.native true maps)
        (List.ofFn fun i => rightRecord (occurrence i) (edge i))=(coefficientCode b : ℤ) ∧
      Radix.positionalHash (p : ℤ) (WeightedGlobalGoodOutputCatalog.key maps)
        (List.ofFn fun i => (occurrence i, (⟨output (edge i),output_mem_vertices (edge i)⟩ :
          WeightedGlobalGoodOutputCatalog.Output m)))=(coefficientCode (a+b) : ℤ) := by sorry
