-- Prove2me | Theorems.Thm_PaleyWeil_coeff_finite_weightedEuler
-- name    : PaleyWeil.coeff_finite_weightedEuler
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:19:17.00622+00:00
-- url     : https://prove2.me/theorems/2c841432-c7f4-4d90-8d5b-a36591d43b61
-- title:
--   Coefficient formula for a finite weighted Euler product
-- statement:
--   Let d(i) be positive integer degrees and w(i) integer weights. If a finite set T contains every index with d(i) ≤ n, then the coefficient of Xⁿ in ∏ᵢ∈T (1 − w(i)Xᵈ⁽ⁱ⁾)⁻¹ is the sum, over finitely supported multiplicity functions m satisfying Σᵢ m(i)d(i) = n, of ∏ᵢ w(i)ᵐ⁽ⁱ⁾.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source research/hec-lean433/RiemannHypothesisCurves/FiniteWeightedEuler.lean lines 109–142; SHA256 d42988791e3b0a458c77b5682af6868195554567c5fd62062a5c14f75fc34356; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_WeightedGeometricSeries
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace PowerSeries
end PowerSeries


/-!
The coefficient identity for a finite weighted Euler product.  The antidiagonal
bijection follows the finite counting argument in Christian Merten's
`WeilConjectures/EulerProductAux.lean` (Apache-2.0), extended here to arbitrary
integer weights and kept entirely finite.
-/
open scoped PowerSeries
open PowerSeries Finset
open PaleyWeil
variable {ι : Type*}

theorem PaleyWeil.coeff_finite_weightedEuler [DecidableEq ι]
    (w : ι → ℤ) (d : ι → ℕ) (T : Finset ι) (n : ℕ)
    (hd : ∀ i, d i ≠ 0) (hT : ∀ i, d i ≤ n → i ∈ T) :
    PowerSeries.coeff n (∏ i ∈ T, weightedGeometric (w i) (d i)) =
      ∑' m : {m : ι →₀ ℕ // (m.sum fun i k ↦ k * d i) = n},
        m.1.prod (fun i k ↦ w i ^ k) := by sorry
