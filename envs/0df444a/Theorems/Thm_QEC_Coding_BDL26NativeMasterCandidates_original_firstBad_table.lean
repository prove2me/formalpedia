-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_original_firstBad_table
-- name    : QEC.Coding.BDL26NativeMasterCandidates.original_firstBad_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:16:46.310206+00:00
-- url     : https://prove2.me/theorems/41b82c52-f628-4a18-bca6-4bd158c4878e
-- title:
--   BDL26 Native Master Candidates: original first Bad table
-- statement:
--   The BDL26 Native Master Candidates construction uses the original first Bad table property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L807-L819
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L807-L819

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

theorem QEC.Coding.BDL26NativeMasterCandidates.original_firstBad_table (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space)
    (r lambda : ℝ) (K : ℕ) (T : BDL26NativeStateRows.Samples (Vertex (P S n))) (m : ℕ) :
    firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        (originalOrderedEvents S n J r)
        (assignment (BDL26NativeStateRows.asTable T)
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable T) m))=
      firstBadFrom (localEvent (eventSupport (P S n) J r) (eventBad (P S n) J r lambda K))
        ((Finset.univ : Finset (Event (P S n) J r)).sort (eventPriorityLE (P S n) J r))
        (assignment (BDL26NativeStateRows.asTable T)
          (counters (X:=fun _ : Vertex (P S n) => Space) (eventSupport (P S n) J r)
            (eventBad (P S n) J r lambda K) (BDL26NativeStateRows.asTable T) m)) := by sorry
