-- Prove2me | Theorems.Thm_QuantumLTF_Membership_lemma_3_1
-- name    : QuantumLTF.Membership.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:38:01.752823+00:00
-- url     : https://prove2.me/theorems/c00d104f-fe1a-48ec-bf45-f2e2aa28a0a1
-- title:
--   Lemma 3.1 — finite-precision reference direction
-- statement:
--   For $n\ge2$ there is a probability distribution on vectors $p\in\mathbb R^n$ whose coordinates are signed fixed-point numbers of $\ell\le C\log n$ bits, with $C$ universal, such that for every $w\in\mathbb S^{n-1}$,
--   $$\Pr\left[\frac1{10}\le|\langle w,p\rangle|\le3\right]\ge\frac45.$$
--   The distribution is fixed before $w$. A reference direction of this kind makes the height function well conditioned and implementable in reversible fixed-point arithmetic.
--
--   Differences from the source:
--   - reading: a randomized classical preprocessing procedure → its output law, a PMF on strings of n·ℓ bits; reason: the printed lemma claims only the output distribution; its cost is counted in the goal
--   - encoding: O(log n) bits per coordinate → one format (ℓ, f) with f ≤ ℓ for all coordinates, coordinates fp_{ℓ,f} of sub-registers; reason: a common format costs only padding; bits include the fractional bits
--   - reading: O(·) in a statement → one universal constant C placed before n and the other parameters; reason: the O(·) of the paper is uniform in all the stated parameters
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.1, p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_addrOf

namespace QuantumLTF.Membership

open QAlgorithms

/-- **Lemma 3.1 (Finite-precision reference direction).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Lemma 3.1, p. 20 (PDF p. 21). For
`n ≥ 2` there is a randomized procedure outputting `p ∈ Rⁿ`, with `O(log n)` bits per coordinate, such
that for every fixed unit `w`, `Pr[1/10 ≤ |⟨w, p⟩| ≤ 3] ≥ 4/5`.

**Formalization Note.** The procedure is its output law `μ`, a `PMF` on the coordinate strings, fixed
before `w`. A string denotes the vector `addrOf n ℓ f` of fixed-point coordinates of its `n`
sub-registers; the `ℓ` here includes the `f` fractional bits. `∃ C` precedes `n`: the constant is
universal. The running cost of the procedure is not part of the printed lemma; it is charged in the
goal's gate count. -/
theorem lemma_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ ℓ f : ℕ, f ≤ ℓ ∧ (ℓ : ℝ) ≤ C * Real.log n ∧ ∃ μ : PMF (Qubits (n * ℓ)),
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          (μ.toOuterMeasure {z | 1 / 10 ≤ |inner ℝ w (addrOf n ℓ f z)| ∧
            |inner ℝ w (addrOf n ℓ f z)| ≤ 3}).toReal ≥ 4 / 5 := by sorry

end QuantumLTF.Membership
