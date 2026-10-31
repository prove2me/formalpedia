-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P23_shortest_winding_vectors
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P23.shortest_winding_vectors
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:32:27.839433+00:00
-- url     : https://prove2.me/theorems/a58d66c6-fb53-4326-94e5-887329e5b645
-- title:
--   Shortest nonzero winding vectors and block counts
-- statement:
--   Let $n\ge2$ and $m\in\mathbb Z^{n-1}$. Define $(C_{k/n})_{rs}=\cos(2\pi k(r-s)/n)$ and
--   $$E(m)=\sum_{j=1}^{n-1}m_j^2-\sum_{j=1}^{n-2}m_jm_{j+1}=\frac2n\sum_{k=1}^{n-1}\sin^2(\pi k/n)m^{\mathsf T}C_{k/n}m.$$
--   For every nonzero $m$, $E(m)\ge1$. Equality holds exactly when $m$ is one constant-sign contiguous block of $\ell$ entries equal to $+1$ or $-1$, with all other entries zero, for some $1\le\ell<n$. For each such $\ell$ the block set is finite and has exactly $2(n-\ell)$ elements. For any block, independent of start and sign,
--   $$m^{\mathsf T}C_{k/n}m=\left(\frac{\sin(\pi k\ell/n)}{\sin(\pi k/n)}\right)^2\quad(1\le k<n).$$
--   These vectors control the leading nontrivial winding terms; the zero vector is excluded from the minimization.
-- source:
--   Entanglement entropy of two disjoint intervals in conformal field theory, arXiv:0905.2069v2, PDF p. 14, Section 4.5, Eqs. (68)–(69)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P23

/-- Source pp.14--15, (68)--(69): minimum one on nonzero integer vectors,
with exactly the contiguous constant-sign blocks as minimizers. Each block
length ell has 2(n-ell) distinct vectors. -/
theorem shortest_winding_vectors (n : ℕ) (hn : 2 ≤ n) :
    (∀ m : Fin (n - 1) → ℤ, windingFourier n m = (windingEnergy n m : ℝ)) ∧
    (∀ m : Fin (n - 1) → ℤ, m ≠ 0 → 1 ≤ windingEnergy n m) ∧
    (∀ m : Fin (n - 1) → ℤ, windingEnergy n m = 1 ↔
      ∃ ell : ℕ, 1 ≤ ell ∧ ell < n ∧ ∃ a : Fin (n - ell), ∃ s : Bool,
        m = windingBlock n ell a.val s) ∧
    (∀ ell : ℕ, 1 ≤ ell → ell < n →
      {m : Fin (n - 1) → ℤ | ∃ a : Fin (n - ell), ∃ s : Bool,
        m = windingBlock n ell a.val s}.Finite ∧
      {m : Fin (n - 1) → ℤ | ∃ a : Fin (n - ell), ∃ s : Bool,
        m = windingBlock n ell a.val s}.ncard = 2 * (n - ell)) ∧
    (∀ ell : ℕ, 1 ≤ ell → ell < n → ∀ a : Fin (n - ell), ∀ s : Bool,
      ∀ k : Fin (n - 1),
      QAlgorithms.Papers.Independent.Information100.P37.quadratic (cosineMatrix n (k.val + 1) (n - 1))
        (fun j => (windingBlock n ell a.val s j : ℝ)) =
      (Real.sin (Real.pi * ((k.val + 1 : ℕ) : ℝ) * (ell : ℝ) / (n : ℝ)) /
        Real.sin (Real.pi * ((k.val + 1 : ℕ) : ℝ) / (n : ℝ))) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P23

end
