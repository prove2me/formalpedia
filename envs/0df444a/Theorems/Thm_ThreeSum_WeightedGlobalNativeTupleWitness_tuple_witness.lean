-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeTupleWitness_tuple_witness
-- name    : ThreeSum.WeightedGlobalNativeTupleWitness.tuple_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:29.878699+00:00
-- url     : https://prove2.me/theorems/de4df534-10c4-4679-ae75-f1153a2121a3
-- title:
--   Weighted Global Native Tuple Witness: tuple witness
-- statement:
--   The Weighted Global Native Tuple Witness construction uses the tuple witness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L55-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L55-L101

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTupleWitness
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeTupleWitness
open Finset TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalCoverGoodMaps
open WeightedGlobalNativeCoverWitness TernaryExtensionEncoding TernaryFixedDictionaries
open scoped BigOperators
variable {p m : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.WeightedGlobalNativeTupleWitness.tuple_witness (maps : I → Weight m p) (B τ : ℕ)
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
