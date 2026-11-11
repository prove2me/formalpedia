-- Prove2me | Theorems.Thm_RQCMoments_orthonormal_zeros
-- name    : RQCMoments.orthonormal_zeros
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:22.008365+00:00
-- url     : https://prove2.me/theorems/5e37c968-3e3e-4445-952f-f48940bd3102
-- title:
--   §2.4 — orthonormal polynomials: existence, uniqueness up to sign, real simple interlacing zeros
-- statement:
--   Let $\nu$ be a probability measure on $\mathbb R$ with finite moments whose support is an infinite set. Then:
--   1. there is a family $q_0,q_1,\dots$ of orthonormal polynomials of $\nu$: $\deg q_n=n$ and $\int q_nq_m\,d\nu=\delta_{n,m}$;
--   2. any two such families agree up to the sign of each polynomial: $q'_n=\pm q_n$;
--   3. for every $n\ge 0$ the zeros of $q_n$ are real and simple, $x_1<\dots<x_n$; each lies in the interior of the convex hull of the support of $\nu$; and they interlace with the zeros $y_1<\dots<y_{n+1}$ of $q_{n+1}$:
--   $$
--   y_i<x_i<y_{i+1}\qquad(1\le i\le n).
--   $$
--
--   These are the classical facts (Szegő, Theorems 3.3.1–3.3.2) on which Gauss quadrature is built (§4.1).
--
--   **Formalization Note** "Real and simple" is stated as: the multiset of roots of $q_n$, counted with multiplicity, is $\{x_1,\dots,x_n\}$ for some strictly increasing $x$. A point $r$ is in the interior of the convex hull of the support iff $\nu((-\infty,r))>0$ and $\nu((r,\infty))>0$.
--
--   Differences from the source:
--
--   - encoding: support of ν is an infinite set → ν(sᶜ) ≠ 0 for every finite s ⊆ ℝ; reason: equivalent for Borel measures on ℝ
--   - encoding: the zeros of q_n are real and simple → (q n).roots = image of a strictly increasing x : Fin n → ℝ (roots counted with multiplicity); reason: a degree-n polynomial with this root multiset has exactly n distinct real roots, each simple
--   - encoding: zeros lie in the interior of the convex hull of the support of ν → 0 < ν(Iio r) and 0 < ν(Ioi r) for each zero r; reason: r is interior to the convex hull of the support iff there is mass strictly on both sides of r
--   - encoding: the zeros of q_n and q_{n+1} interlace → y_i < x_i < y_{i+1} for the increasing enumerations x of the zeros of q_n and y of q_{n+1}; reason: the standard meaning of interlacing of n and n+1 simple zeros
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), §2.4, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RQCMoments_IsOPMeasure
import Definitions.Def_RQCMoments_IsOrthonormalFamily

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **§2.4, orthonormal polynomials and their zeros** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), §2.4, p.15, PDF p.17).
Let `ν` be a probability measure on `ℝ` with finite moments and infinite support. Then
1. orthonormal polynomials `q₀, q₁, …` (`deg qₙ = n`, `∫ qₙ qₘ dν = δ_{n,m}`) exist;
2. they are unique up to sign;
3. for every `n`, the zeros of `qₙ` are real and simple (`qₙ` has `n` distinct real roots
   `x₁ < ⋯ < xₙ`), they lie in the interior of the convex hull of the support of `ν`, and they
   interlace with the zeros `y₁ < ⋯ < y_{n+1}` of `q_{n+1}`: `yᵢ < xᵢ < y_{i+1}`.

**Formalization Note** "Real and simple" is: the root multiset of `qₙ` (with multiplicity) is the
image of a strictly increasing `x : Fin n → ℝ`. A point `r` lies in the interior of the convex hull
of the support iff `ν((−∞, r)) > 0` and `ν((r, ∞)) > 0`. -/
theorem orthonormal_zeros (ν : Measure ℝ) (hν : IsOPMeasure ν) :
    (∃ q : ℕ → Polynomial ℝ, IsOrthonormalFamily ν q) ∧
    (∀ q q' : ℕ → Polynomial ℝ, IsOrthonormalFamily ν q → IsOrthonormalFamily ν q' →
      ∀ n, q' n = q n ∨ q' n = -q n) ∧
    ∀ q : ℕ → Polynomial ℝ, IsOrthonormalFamily ν q → ∀ n : ℕ,
      ∃ x : Fin n → ℝ, StrictMono x ∧ (q n).roots = Multiset.map x Finset.univ.val ∧
        (∀ i, 0 < ν (Set.Iio (x i)) ∧ 0 < ν (Set.Ioi (x i))) ∧
        ∃ y : Fin (n + 1) → ℝ, StrictMono y ∧ (q (n + 1)).roots = Multiset.map y Finset.univ.val ∧
          ∀ i : Fin n, y i.castSucc < x i ∧ x i < y i.succ := by sorry

end RQCMoments
