-- Prove2me | Theorems.Thm_RegevLWE_SubsetSum_cauchy_schwarz_l2
-- name    : RegevLWE.SubsetSum.cauchy_schwarz_l2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:37.842993+00:00
-- url     : https://prove2.me/theorems/359fc5d6-3e5d-454d-b710-5c9b163ad0d0
-- title:
--   Proof of Claim 5.3, p. 34:37 — Cauchy–Schwarz Σ_h|P_g(h) − 1/|G|| ≤ |G|^{1/2}(Σ_h(P_g(h) − 1/|G|)²)^{1/2} and the ℓ₂ identity
-- statement:
--   Let $G$ be a finite abelian group, $l \ge 0$, $g \in G^l$, and let $P_g$ be the distribution of the sum of a uniformly random subset of $g_1, \dots, g_l$. Then
--
--   1. (Cauchy–Schwarz over the $|G|$ points of $G$)
--   $$\sum_{h \in G} \Bigl|P_g(h) - \frac{1}{|G|}\Bigr| \le |G|^{1/2}\Bigl(\sum_{h \in G}\Bigl(P_g(h) - \frac{1}{|G|}\Bigr)^2\Bigr)^{1/2};$$
--   2. (the $\ell_2$ identity, using $\sum_h P_g(h) = 1$)
--   $$\sum_{h \in G}\Bigl(P_g(h) - \frac{1}{|G|}\Bigr)^2 = \sum_{h \in G} P_g(h)^2 - \frac{1}{|G|}.$$
--
--   These are the first two steps of the final chain of the proof of Claim 5.3, which bound the statistical distance of $P_g$ from uniform by its $\ell_2$ norm, pointwise in $g$.
--
--   **Formalization Note** The left-hand side of the first item is `statDistUniform g`; square roots are `Real.sqrt`.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:37, proof of Claim 5.3, second display (first inequality and the equality that follows)

import Mathlib
import Definitions.Def_RegevLWE_SubsetSum_Basic

open Finset

namespace RegevLWE.SubsetSum

/-- Proof of Claim 5.3 (Regev, J. ACM 2009, p. 34:37, second display, first two steps), pointwise in
`g`: Cauchy–Schwarz over the `|G|` points of `G`,
`∑_h |P_g(h) − 1/|G|| ≤ |G|^{1/2} (∑_h (P_g(h) − 1/|G|)²)^{1/2}`, and the identity
`∑_h (P_g(h) − 1/|G|)² = ∑_h P_g(h)² − 1/|G|`. -/
theorem cauchy_schwarz_l2 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {l : ℕ}
    (g : Fin l → G) :
    statDistUniform g ≤
        Real.sqrt (Fintype.card G) * Real.sqrt (∑ h, (P g h - 1 / (Fintype.card G : ℝ)) ^ 2) ∧
      ∑ h, (P g h - 1 / (Fintype.card G : ℝ)) ^ 2 = ∑ h, P g h ^ 2 - 1 / (Fintype.card G : ℝ) := by sorry

end RegevLWE.SubsetSum
