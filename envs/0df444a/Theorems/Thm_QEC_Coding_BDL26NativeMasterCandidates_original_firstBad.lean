-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_original_firstBad
-- name    : QEC.Coding.BDL26NativeMasterCandidates.original_firstBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:09:59.619859+00:00
-- url     : https://prove2.me/theorems/221a1474-c786-44f0-b86a-7a2e50815c31
-- title:
--   BDL26 Native Master Candidates: original first Bad
-- statement:
--   The BDL26 Native Master Candidates construction uses the original first Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L799-L805
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L799-L805

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Mathlib.Data.List.Sublists
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeMasterCandidates
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
noncomputable section
open scoped Classical

theorem QEC.Coding.BDL26NativeMasterCandidates.original_firstBad (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (z : Vertex (P S n) → Space) :
    firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        (originalOrderedEvents S n J r) z=
      firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        ((Finset.univ : Finset (Event (P S n) J r)).sort (eventPriorityLE (P S n) J r)) z := by sorry
