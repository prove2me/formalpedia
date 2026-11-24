-- Prove2me | Theorems.Thm_SameStatePairs_orbit_level_failure
-- name    : SameStatePairs.orbit_level_failure
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T21:02:42.852801+00:00
-- url     : https://prove2.me/theorems/7888b17a-87aa-4c5b-a812-939187ee94af
-- title:
--   Proposition 1: orbit-level failure of uniqueness for same-state pairs
-- statement:
--   Let $Z$ be a finite world with $p(z)>0$, $\sum_zp(z)=1$ and $d_z=|Z|$, and let $\pi=\operatorname{diag}(p)$, with the hard-whitening objective in dimension $k$. Let $1\le k<d_z-1$ and $d_z-1\ge 2k$. Then:
--
--   1. There exist global minimisers $f,g:Z\to\mathbb{R}^k$ such that
--   $$\mathbb{E}\|f-Qg\|^2=2k\qquad\text{for every }Q\in O(k).$$
--   2. This is the maximum possible: for any centred, whitened $f,g$, some $Q\in O(k)$ has $\mathbb{E}\|f-Qg\|^2\le2k$. So the best-rotation residual $\min_Q\mathbb{E}\|f-Qg\|^2$ of the pair in 1 equals $2k$.
--   3. If $|Z|=3$ and $k=1$, any two centred unit-variance state functions $f,g$ with $\mathbb{E}[fg]=0$ are global minimisers and have $\mathbb{E}|f-Qg|^2=2$ for both $Q\in O(1)=\{\pm1\}$.
--
--   Here $\mathbb{E}$ is the expectation over $z\sim p$. Two global minimisers can therefore be as far apart as two whitened encoders can be, so the minimiser set is not close to a single rotation orbit.
--
--   **Formalization Note** The hypothesis $d_z-1\ge 2k$ is written $2k+1\le|Z|$, and $k<d_z-1$ is written $k+1<|Z|$. "The maximum possible" is stated as item 2, the bound that the paper's proof gives. Item 3 is stated for functions into $\mathbb{R}^1$, under the hypothesis $|Z|=3$.
-- source:
--   Xin Li, Same-State Pairs Make One JEPA Proof of the Platonic Representation Hypothesis Vacuous: A Correction and a Gauge Ledger, arXiv:2611.16182v1 (2026), Section 2.2, Proposition 1, eq. (1), p. 4

import Mathlib
import Definitions.Def_SameStatePairs_Basic

open Matrix

namespace SameStatePairs

theorem orbit_level_failure {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (hk : 1 ≤ k) (hkZ : k + 1 < Fintype.card Z) (h2k : 2 * k + 1 ≤ Fintype.card Z) :
    (∃ f g : Z → Fin k → ℝ, IsGlobalMin p (sameStateLaw p) f ∧
      IsGlobalMin p (sameStateLaw p) g ∧
      ∀ Q : Matrix.orthogonalGroup (Fin k) ℝ, rotResidual p f g Q = 2 * k) ∧
    (∀ f g : Z → Fin k → ℝ, IsCentered p f → IsWhitened p f → IsCentered p g → IsWhitened p g →
      ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, rotResidual p f g Q ≤ 2 * k) ∧
    (Fintype.card Z = 3 →
      ∀ f g : Z → Fin 1 → ℝ, IsCentered p f → IsWhitened p f → IsCentered p g →
        IsWhitened p g → ∑ z, p z * f z 0 * g z 0 = 0 →
        IsGlobalMin p (sameStateLaw p) f ∧ IsGlobalMin p (sameStateLaw p) g ∧
        ∀ Q : Matrix.orthogonalGroup (Fin 1) ℝ, rotResidual p f g Q = 2) := by sorry

end SameStatePairs
