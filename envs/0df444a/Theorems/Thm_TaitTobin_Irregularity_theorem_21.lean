-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_theorem_21
-- name    : TaitTobin.Irregularity.theorem_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:41.152981+00:00
-- url     : https://prove2.me/theorems/527598c3-3226-402b-98dc-df6e29ada4b4
-- title:
--   Theorem 21, p. 20 — for large n, a connected graph maximizing λ₁ − d is a pineapple (Aouchiche et al.)
-- statement:
--   There is $N$ such that for every $n \ge N$ the following holds. Let $G$ be a connected graph on $n$ vertices that maximizes
--   $$\lambda_1(G) - d(G), \qquad d(G) = \frac{2e(G)}{n},$$
--   among all connected graphs on $n$ vertices, where $\lambda_1$ is the largest adjacency eigenvalue. Then $G$ is a pineapple graph: there are $p, q \ge 0$ with $p + q = n$ such that
--   $$G \cong PA(p,q),$$
--   the complete graph $K_p$ with $q$ pendant vertices all attached to one vertex of the clique.
--
--   This proves, for all sufficiently large $n$, the conjecture of Aouchiche, Bell, Cvetković, Hansen, Rowlinson, Simić and Stevanović (2008), found by computer search, on the most irregular connected graphs in the sense of spectral radius minus average degree.
--
--   **Formalization Note** Only the shape is asserted: the clique size $p$ is not pinned. The paper attributes the optimal clique size $\lceil n/2\rceil + 1$ to Aouchiche et al. (Section 6) and does not prove it. The statement is one-directional; not every pineapple is a maximizer. $G \cong PA(p,q)$ is a graph isomorphism between the vertex sets $\{0,\dots,n-1\}$ and $\{0,\dots,p+q-1\}$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 20, Theorem 21 (Conjecture 3, p. 2)

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Theorem 21, p. 20 (the conjecture of Aouchiche et al., Conjecture 3, p. 2): for `n` large, every
connected graph on `n` vertices maximizing `λ₁ − d` is isomorphic to a pineapple `PA(p, q)` with
`p + q = n`. -/
theorem theorem_21 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsIrregMax G →
    ∃ p q : ℕ, p + q = n ∧ Nonempty (G ≃g pineapple p q) := by sorry
end TaitTobin.Irregularity
