-- Prove2me | Theorems.Thm_PaleyWeil_splitCharacterSum_even_reduction
-- name    : PaleyWeil.splitCharacterSum_even_reduction
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:23.933249+00:00
-- url     : https://prove2.me/theorems/ceee8e3d-f9d6-4446-a0f9-06adf19c25e6
-- title:
--   Inversion at a root gives the exact even-degree character correction
-- statement:
--   Let s be an even-cardinality finite subset of a finite field and let a ∈ s. Put s′ = {(b−a)⁻¹ : b ∈ s, b ≠ a} and c = ∏ᵦ∈s∖{a}(a−b). Then splitCharacterSum(s) + 1 = χ(c)·splitCharacterSum(s′).
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitEvenReduction.lean lines 77–104; SHA256 5a6c810fae82eeebe6d3371a0784ce36a0927f01247986614079cbfa99224a5a; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitEvenReduction
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil


open Finset
open PaleyWeil
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem PaleyWeil.splitCharacterSum_even_reduction (s : Finset K) (a : K) (ha : a ∈ s)
    (heven : Even s.card) :
    splitCharacterSum s + 1 = quadraticChar K (reciprocalScale s a) *
      splitCharacterSum (reciprocalRoots s a) := by sorry
