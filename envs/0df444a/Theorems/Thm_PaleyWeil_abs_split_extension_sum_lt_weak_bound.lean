-- Prove2me | Theorems.Thm_PaleyWeil_abs_split_extension_sum_lt_weak_bound
-- name    : PaleyWeil.abs_split_extension_sum_lt_weak_bound
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:34:18.888396+00:00
-- url     : https://prove2.me/theorems/e55373de-0db3-4d85-8384-ed32400bcfa3
-- title:
--   Weak character-sum bound over every finite extension
-- statement:
--   Let L/K be a finite extension of finite fields with L of odd characteristic, and let s ⊆ K contain m ≥ 3 elements. If |L| > 6m, then |Σₓ∈L χₗ(∏ₐ∈s(x−a))| < 5m√|L|, where the roots are embedded into L.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitWeakBound.lean lines 66–89; SHA256 a085700b582884c017a4077a03b16064ed535c978747d8cc59a9db8d448fef66; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial Finset
open PaleyWeil

theorem PaleyWeil.abs_split_extension_sum_lt_weak_bound {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L]
    (hL : ringChar L ≠ 2) (s : Finset K) (hs3 : 3 ≤ s.card)
    (hq : 6 * s.card < Fintype.card L) :
    |((∑ x : L, quadraticChar L (∏ a ∈ s, (x - algebraMap K L a)) : ℤ) : ℝ)| <
      5 * (s.card : ℝ) * Real.sqrt (Fintype.card L) := by sorry
