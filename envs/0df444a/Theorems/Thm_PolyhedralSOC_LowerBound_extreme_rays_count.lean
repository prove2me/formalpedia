-- Prove2me | Theorems.Thm_PolyhedralSOC_LowerBound_extreme_rays_count
-- name    : PolyhedralSOC.LowerBound.extreme_rays_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:46:48.772869+00:00
-- url     : https://prove2.me/theorems/35b4584f-264e-499c-832d-9dd34b9be04c
-- title:
--   Proposition 3.1, proof — a line-free polyhedral cone with $q$ inequalities is the conic hull of at most $2^q$ extreme rays
-- statement:
--   Let $V$ be a finite-dimensional real vector space and $A:V\to\mathbb R^q$ a linear map, and let
--   $$K=\{z\in V\mid Az\ge 0\}$$
--   be the polyhedral cone defined by these $q$ homogeneous linear inequalities. Suppose $K$ contains no line ($z\in K$ and $-z\in K$ imply $z=0$). Then there is a finite set $R\subseteq V$ with
--   $$|R|\le 2^q$$
--   such that every $r\in R$ is nonzero and spans an **extreme ray** $\{sr\mid s\ge0\}$ of $K$ (a face of $K$), and $K$ is the conic hull of $R$: every $z\in K$ is a nonnegative combination $z=\sum_{r\in R}c_r r$, $c_r\ge 0$, and every such combination lies in $K$.
--
--   Since every extreme ray of the conic hull of $R$ is spanned by an element of $R$, this says that $K$ has at most $2^q$ extreme rays and is their conic hull. It is the counting step "$K$ is a conic hull of its extreme rays. Let $N$ be the number of extreme rays of $K$; one clearly has $N\le 2^q$" of the lower-bound proof.
--
--   **Formalization Note** "Extreme ray" is the ray $\{sr\mid s\ge 0\}$ being an extreme subset of $K$ in the sense of Mathlib's `IsExtreme` (if a point of the ray lies in the open segment between two points of $K$, both points lie in the ray). Rays are counted by one representative each, so $|R|$ bounds the number of rays, not of vectors.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 202, Proposition 3.1, proof ("K is a conic hull of its extreme rays … N ≤ 2^q")

import Mathlib

namespace PolyhedralSOC.LowerBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 3.1, proof, p. 202 (PDF p. 10):
a polyhedral cone `K = {z | A z ≥ 0}` given by `q` homogeneous linear inequalities that
"does not contain lines" is "a conic hull of its extreme rays", and the number `N` of its extreme
rays satisfies `N ≤ 2^q`. Stated for a linear map `A : V → ℝ^q` on a finite-dimensional real
vector space `V`: there is a finite set `R` of at most `2^q` nonzero vectors, each spanning an
extreme ray `{s • r | s ≥ 0}` of `K` (a face of `K` in the sense of Mathlib's `IsExtreme`), whose
conic hull is `K`. Since every extreme ray of the conic hull of `R` is spanned by an element of
`R`, this says exactly that `K` has at most `2^q` extreme rays and is their conic hull. -/
theorem extreme_rays_count {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {q : ℕ} (A : V →ₗ[ℝ] (Fin q → ℝ))
    (hK : ∀ z : V, 0 ≤ A z → 0 ≤ A (-z) → z = 0) :
    ∃ R : Finset V, R.card ≤ 2 ^ q ∧
      (∀ r ∈ R, r ≠ 0 ∧
        IsExtreme ℝ {z : V | 0 ≤ A z} {x : V | ∃ s : ℝ, 0 ≤ s ∧ x = s • r}) ∧
      {z : V | 0 ≤ A z} =
        {z : V | ∃ c : V → ℝ, (∀ r ∈ R, 0 ≤ c r) ∧ z = ∑ r ∈ R, c r • r} := by sorry

end PolyhedralSOC.LowerBound
