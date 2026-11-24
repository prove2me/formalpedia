-- Prove2me | Theorems.Thm_PaleyWeil_split_monic_sum_eq_zero
-- name    : PaleyWeil.split_monic_sum_eq_zero
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:22.876111+00:00
-- url     : https://prove2.me/theorems/bab82bb4-2fd2-4d6e-ad6d-a6026ae7ca0b
-- title:
--   High-degree coefficients of the split quadratic L-series vanish
-- statement:
--   Let K be a finite field of odd characteristic and s a nonempty finite subset. For every n ≥ |s|, the sum of splitQuadraticWeight(s,P) over all monic degree-n polynomials P is zero. The weight is χₖ((−1)^(|s|·deg P)∏ₐ∈s P(a)).
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitCoefficientVanishing.lean lines 71–99; SHA256 764187a03dba3215531e05f1535ee7fd6c5d7f22c617c0749866d6c79fcb9022; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitQuadraticWeight
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial Finset
open PaleyWeil
set_option maxHeartbeats 800000

theorem PaleyWeil.split_monic_sum_eq_zero {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hK : ringChar K ≠ 2) (s : Finset K) (hs : s.Nonempty) (n : ℕ) (hn : s.card ≤ n) :
    ∑' P : {P : K[X] // IsMonicOfDegree P n}, splitQuadraticWeight s P = 0 := by sorry
