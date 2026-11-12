-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_eligible_support
-- name    : QEC.Coding.BDL26NativeMasterCandidates.eligible_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:18:58.158676+00:00
-- url     : https://prove2.me/theorems/43132db1-ba4c-4921-90f9-845267ce0690
-- title:
--   BDL26 Native Master Candidates: eligible support
-- statement:
--   The BDL26 Native Master Candidates construction uses the eligible support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L741-L754
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L741-L754

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

theorem QEC.Coding.BDL26NativeMasterCandidates.eligible_support (S : OddScale) (n : ℕ) (J : Vertex (P S n) → Space) (r : ℝ)
    (e : Event (P S n) J r) :
    ∃!row : FourCodes × Option (List (Index S n)),row∈Rows S n ∧
      Rep S n row.1 (eventToMaster (P S n) J r e) ∧
      ∃U,row.2=some U ∧ U.Nodup ∧ U.length≤12 ∧
        ∀i,i∈U ↔ BDL26NativeStateRows.decode S n i∈eventSupport (P S n) J r e := by sorry
