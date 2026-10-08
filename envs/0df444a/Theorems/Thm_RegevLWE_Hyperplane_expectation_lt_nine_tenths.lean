-- Prove2me | Theorems.Thm_RegevLWE_Hyperplane_expectation_lt_nine_tenths
-- name    : RegevLWE.Hyperplane.expectation_lt_nine_tenths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:52.680983+00:00
-- url     : https://prove2.me/theorems/0fa4ed19-0009-448f-8bd5-c4275629a4ea
-- title:
--   Proof of Lemma 3.15, p. 34:31 — the expectation is at most (1/√2)(1 + ε) < 0.9
-- statement:
--   Let $L \subset \mathbb{R}^n$ be a lattice, let $0 < \epsilon \le \tfrac1{10}$ and $r > 0$ with $r \ge \sqrt2\,\eta_\epsilon(L)$, and let $w \in \mathbb{R}^n$ be a unit vector. Then
--   $$\mathop{\mathrm{Exp}}_{x \sim D_{L,r}}\Bigl[\exp\bigl(-\pi(\langle w, x\rangle/r)^2\bigr)\Bigr] \le \frac{1}{\sqrt2}(1 + \epsilon) < 0.9 .$$
--
--   This combines the expectation chain with $\rho_r(L) \ge \det(L^*)\,r^n$. Since $\exp(-\pi(\langle w, x\rangle/r)^2) = 1$ for every $x$ orthogonal to $w$ and is at most $1$ everywhere, the expectation upper-bounds the probability that $x$ lies in any subspace orthogonal to $w$, which gives Lemma 3.15.
--
--   **Formalization Note** The expectation is $\sum_{x \in L} D_{L,r}(x)\exp(-\pi\langle w, x\rangle^2/r^2)$; the paper's coordinate $x_1$ (after its "without loss of generality" rotation) is $\langle w, x\rangle$ for a unit vector $w$. $\epsilon > 0$ and $r > 0$ are the paper's standing readings.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:31, proof of Lemma 3.15, last sentence ('Therefore, the expectation above is at most …')

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian

namespace RegevLWE.Hyperplane

theorem expectation_lt_nine_tenths {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {ε r : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (hr : 0 < r) (h : Real.sqrt 2 * RegevLWE.GaussConv.smoothingParam L ε ≤ r)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) :
    (∑' x : L, discreteGaussian L r x *
        Real.exp (-Real.pi * (inner ℝ w (x : EuclideanSpace ℝ (Fin n))) ^ 2 / r ^ 2)) ≤
      1 / Real.sqrt 2 * (1 + ε) ∧
    1 / Real.sqrt 2 * (1 + ε) < 9 / 10 := by sorry

end RegevLWE.Hyperplane
