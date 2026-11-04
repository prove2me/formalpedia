-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPreparedOriginals_of_output
-- name    : ThreeSum.WeightedGlobalPreparedOriginals.of_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:03:05.014684+00:00
-- url     : https://prove2.me/theorems/7134dd47-f64f-467b-b222-f31d289cff7c
-- title:
--   Weighted Global Prepared Originals: of output
-- statement:
--   Positive actual color preparation supplies the entire original-input
--   prefix certificate for the exact finite field found by the global backend.
--   The coefficient reads are derived from its real menu, not supplied as advice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L191-L235
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPreparedOriginals.lean#L191-L235

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPreparedOriginals
open Light LightWeightedGlobalColorPreparation LightWeightedGlobalColorPreparationProof
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLayout
open WeightedGlobalArenaSeedData TernarySignedReduction TernarySignedLayout
open WeightedGlobalArenaSelectedSigned TernaryExtensionEncoding
set_option maxHeartbeats 6000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
variable {d c : ℕ} [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus p d c))]

theorem ThreeSum.WeightedGlobalPreparedOriginals.of_output {n free U R J backend radix C0 weightCap queryTime : ℕ}
    (hd : 0<d) (μ ν : ℕ→ℤ) (color : Coloring.Parameter (LightColorParametersCosts.width n))
    (x : Fin n→ℤ) (ret : ℤ)
    (H : LightWeightedGlobalColorPreparationProof.Output μ ν free U R J (p^d)
      (LightExtensionBackendLayout.physical backend d (p^d) J) radix color x ret)
    (hret : ret≠0) (hx : ∀i,|x i|≤(U:ℤ)) (hb : 1<radix) (hp : radix<p)
    (hbackend : backend+LightExtensionBackendLayout.reserve d p (p^d) J≤free)
    (hMenu : LightWeightedGlobalGlobalPreludeProof.Menu μ backend d p (p^d) J c) :
    ∃A B C : List ℤ,
      Metadata n U A B C ∧ A≠[] ∧ B≠[] ∧ C≠[] ∧
      LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.av free n) n
        (ColorClassLists.classList color x 0 1) A ∧
      LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.bv free n) n
        (ColorClassLists.classList color x 1 1) B ∧
      LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.cv free n) n
        (ColorClassLists.classList color x 2 (-1)) C ∧
      Seg ν (headerAt free n (LightColorParametersCosts.width n))
        (header free n U R J (p^d) (LightExtensionBackendLayout.physical backend d (p^d) J) A B C) ∧
      WeightedGlobalArenaPrefixInputs.Originals (input free n U J C0 weightCap queryTime A B C)
        (inputs free n J (LightExtensionBackendLayout.physical backend d (p^d) J) A B C)
        ((p^d)*(p^d)) radix radix n (WeightedGlobalComputedExtensionMenu.functional (p:=p) (c:=c) hd)
        (WeightedGlobalArenaFamilyBudget.seedAt (WeightedGlobalComputedExtensionMenu.seeds (p:=p) (d:=d) (c:=c)))
        (left U radix J (fun i => B.getD i 0)) (right U radix J (fun i => C.getD i 0))
        (requester U radix J (fun i => A.getD i 0)) ν := by sorry
