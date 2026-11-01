-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P81_emergent_gauge_convex_hull
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P81.emergent_gauge_convex_hull
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:00:28.771526+00:00
-- url     : https://prove2.me/theorems/d66cb833-a87f-4ef5-8d96-4d4ea9493ce0
-- title:
--   Emergent gauge couplings satisfy the many-parameter convex-hull condition
-- statement:
--   Let $d>4$, $k\ge1$, $N_i\in\mathbb N_{>0}$, $\Lambda>0$, and $m_i>0$, for $1\le i\le k$. Define
--
--   $$C_d=\sqrt{\frac{d-2}{8\pi(d-3)}},\qquad q_i=\frac1{\sqrt{N_i\Lambda^{d-4}}},\qquad G=\frac1{\sum_i N_i\Lambda^{d-2}},\qquad z_i=\frac{C_dq_i}{m_i\sqrt G}\,e_i,$$
--
--   where $e_i$ is the $i$th Euclidean coordinate vector. If $m_i^2<C_d^2\Lambda^2$ for every $i$, then
--
--   $$\{x\in\mathbb R^k:\|x\|_2\le1\}\subseteq\operatorname{conv}\{z_i,-z_i:1\le i\le k\}.$$
--
--   This is the Cheung–Remmen convex-hull bound for the normalized effective model relations used in this section. Both particles and antiparticles are included; the four-dimensional logarithmic coupling formula is outside this statement.
-- source:
--   Symmetries in quantum field theory and quantum gravity, arXiv:1810.05338v2, PDF p. 129, §9: many-parameter emergent-gauge convex-hull bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P81

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P81

open scoped BigOperators ComplexConjugate Manifold ContDiff

/-- Section 9, PDF pp.126--129, especially (9.9)--(9.17).
This is the convex-hull result under the normalized effective large-N model relations,
not a universal weak gravity conjecture. The logarithmic d=4 regime is excluded. -/
theorem emergent_gauge_convex_hull {k : ℕ} (hk : 0 < k) (d : ℕ) (hd : 4 < d)
    (multiplicity : Fin k → ℕ) (hN : ∀ i, 0 < multiplicity i)
    (cutoff : ℝ) (hcutoff : 0 < cutoff) (mass : Fin k → ℝ)
    (hmass : ∀ i, 0 < mass i)
    (hlight : ∀ i, mass i ^ 2 < (extremalConstant d) ^ 2 * cutoff ^ 2) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆
      convexHull ℝ (realizedChargeVectors d multiplicity cutoff mass) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P81

end
