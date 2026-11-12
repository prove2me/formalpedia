-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeMasterCandidates_quadruples_bound
-- name    : QEC.Coding.BDL26NativeMasterCandidates.quadruples_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:08:27.569343+00:00
-- url     : https://prove2.me/theorems/61cc70df-e6fe-439b-bbd9-fc304a2309bf
-- title:
--   BDL26 Native Master Candidates: quadruples bound
-- statement:
--   Three structural append levels and one metered fourth-choice map.
--   The terms count leaves, cursor nodes and exhausted suffixes separately.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L236-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeMasterCandidates.lean#L236-L263

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

theorem QEC.Coding.BDL26NativeMasterCandidates.quadruples_bound {A B : Type*} (f : A → A → A → A → Run B)
    (L : List A) (p q : ℕ)
    (h : ∀a b c d,(f a b c d).operations≤p ∧ (f a b c d).allocations≤q) :
    (quadruplesQ f L).value.length=Nat.choose L.length 4 ∧
      (quadruplesQ f L).operations≤Nat.choose L.length 4*(p+9)+
        4*(L.length+Nat.choose L.length 2+Nat.choose L.length 3)+
          1+L.length+Nat.choose L.length 2 ∧
      (quadruplesQ f L).allocations≤Nat.choose L.length 4*(q+4)+
        L.length+Nat.choose L.length 2+Nat.choose L.length 3 := by sorry
