-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapX09_l1Coherence_convex
-- name    : QAlgorithms.Papers.RoadmapX09.l1Coherence_convex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:23:05.418999+00:00
-- url     : https://prove2.me/theorems/429afafd-e671-41f2-ac4b-ecbc74064f1e
-- title:
--   Convexity of the l1-norm of coherence
-- statement:
--   Fix an orthonormal reference basis in a finite-dimensional Hilbert space of dimension $d\ge 1$. For a density matrix $\rho$, define its $l_1$-norm of coherence in this basis by $C_{l_1}(\rho)=\sum_{i\ne j}|\rho_{ij}|$, where the absolute value is the complex modulus and both ordered off-diagonal entries are counted. Let $\rho_1,\ldots,\rho_m$ be any finite family of density matrices on this same space, and let $p_1,\ldots,p_m$ be real numbers with $p_a\ge 0$ and $\sum_a p_a=1$. Then
--
--   $$
--   \sum_{a=1}^{m}p_a C_{l_1}(\rho_a)\ge C_{l_1}\!\left(\sum_{a=1}^{m}p_a\rho_a\right).
--   $$
--
--   This is condition (C3) for the coherence functional of Eq. (9): mixing quantum states cannot increase coherence above the weighted average of the component coherences.
-- source:
--   Quantifying Coherence, arXiv:1311.0275v3, (C3); lp-norms, Eq. (9), PDF p. 3. https://arxiv.org/abs/1311.0275v3 . PDF SHA-256: c70b296ff2628a49bfb6ffd3e0abb02ad1aa50162dec040cf32047eb3a450825.

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapX09

/-- Baumgratz, Cramer and Plenio, *Quantifying Coherence*, arXiv:1311.0275v3,
PDF p.3: condition (C3) for the l1 coherence of Eq. (9), asserted in the
`lp-norms` paragraph and justified by Eq. (7) and the following norm argument.
All density matrices use the same fixed orthonormal reference basis in dimension
`d >= 1` (pp.1-2); finite dimensionality is explicit in the Outlook (p.4).
The mixture is the computed convex combination, and zero weights are allowed. -/
theorem l1Coherence_convex (d m : ℕ) (hd : 1 ≤ d)
    (p : Fin m → ℝ) (rho : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hrho : ∀ a, IsDensityMatrix (rho a))
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    (∑ a, p a * Coherence.l1Coherence (rho a)) ≥
      Coherence.l1Coherence (∑ a, (p a : ℂ) • rho a) := by sorry

end QAlgorithms.Papers.RoadmapX09
