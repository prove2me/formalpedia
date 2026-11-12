-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_quadruples_census
-- name    : QEC.Coding.BDL26NativeMasterCandidates.quadruples_census
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:15:02.294369+00:00
-- url     : https://prove2.me/theorems/6d0123c8-26cb-41c5-aa86-7a382482d9d6
-- title:
--   BDL26 Native Master Candidates: quadruples census
-- statement:
--   Exact overhead census of the SAME suffix/map/append interpreter: C leaves,
--   K nonempty cursor nodes and E exhausted suffixes. The 9C/4C terms are map
--   3C/1C plus all THREE append copies 6C/3C. No length scan computes a counter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L363-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L363-L374

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

theorem QEC.Coding.BDL26NativeMasterCandidates.quadruples_census {A : Type*} (L : List A) :
    let measured := quadruplesQ
      (fun a b c d => (⟨(a,b,c,d),0,0⟩ : Run (Quad A))) L
    measured.value.length=Nat.choose L.length 4 ∧
      measured.operations=9*Nat.choose L.length 4+
        4*(L.length+Nat.choose L.length 2+Nat.choose L.length 3)+
          1+L.length+Nat.choose L.length 2 ∧
      measured.allocations=4*Nat.choose L.length 4+
        L.length+Nat.choose L.length 2+Nat.choose L.length 3 := by sorry
