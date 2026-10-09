-- Prove2me | Theorems.Thm_SphereSOS_Rate_proposition_5
-- name    : SphereSOS.Rate.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:20:23.847099+00:00
-- url     : https://prove2.me/theorems/2a5c02fd-2ef0-4775-a34a-ee369b3c786a
-- title:
--   Proposition 5, pp. 6, 15 — $\|f_{2k}\|_\infty\le B_{2n}\|f\|_\infty$ with $B_{2n}$ independent of $d$; $B_2\le2$, $B_4\le9$
-- statement:
--   1. For every $n\ge0$ there is a constant $B_{2n}$ such that, in every dimension $d$, for every homogeneous polynomial $f$ of degree $2n$ with spherical harmonic decomposition $f=\sum_{k=0}^nf_{2k}$ on $S^{d-1}$ ($f_{2k}\in\mathcal H^d_{2k}$),
--   $$\|f_{2k}\|_\infty\le B_{2n}\,\|f\|_\infty\qquad(k=0,\dots,n),$$
--   where $\|\cdot\|_\infty$ is the maximum of the absolute value over $S^{d-1}$.
--   2. One may take $B_2=2$ and $B_4=9$, in every dimension.
--
--   The point is that $B_{2n}$ depends on $n$ only: harmonic projection of forms of fixed degree is bounded in sup norm uniformly in the dimension. This is what makes the constants of Theorem 2 independent of $d$.
--
--   **Formalization Note** "$B$ works in dimension $d$" is the predicate of the setting definition (harmonic decomposition written as the polynomial identity $f=\sum_k\|x\|^{2(n-k)}h_k$ with $h_k$ homogeneous harmonic of degree $2k$; $\|f\|_\infty\le M$ pointwise). The constant is chosen before $d$.
-- source:
--   Fang, Fawzi, The sum-of-squares hierarchy on the sphere, and applications in quantum information theory, arXiv:1908.05155v1, p. 6, Proposition 5; p. 15, Proposition 5 (restatement)

import Mathlib
import Definitions.Def_SphereSOS_Rate_Setting

namespace SphereSOS.Rate

theorem proposition_5 :
    (∀ n : ℕ, ∃ B : ℝ, ∀ d : ℕ, PropFiveBound n d B) ∧
    (∀ d : ℕ, PropFiveBound 1 d 2 ∧ PropFiveBound 2 d 9) := by sorry

end SphereSOS.Rate
