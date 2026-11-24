-- Prove2me | Theorems.Thm_PaleyWeil_curve_count_eq_card_add_character_sum
-- name    : PaleyWeil.curve_count_eq_card_add_character_sum
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T14:18:22.363161+00:00
-- url     : https://prove2.me/theorems/1ef432d6-0f46-4bf2-be68-ad20f27f85f5
-- title:
--   Affine quadratic point count equals field size plus character sum
-- statement:
--   For any polynomial f over a finite field F of odd characteristic, the number of affine solutions to y² = f(x) equals |F| + Σₓ∈F χꜰ(f(x)), as an integer identity.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/SplitWeakBound.lean lines 26–47; SHA256 a085700b582884c017a4077a03b16064ed535c978747d8cc59a9db8d448fef66; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

theorem PaleyWeil.curve_count_eq_card_add_character_sum {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (hF : ringChar F ≠ 2) (f : F[X]) :
    (Fintype.card {p : F × F // p.2 ^ 2 = f.eval p.1} : ℤ) =
      (Fintype.card F : ℤ) + ∑ x : F, quadraticChar F (f.eval x) := by sorry
