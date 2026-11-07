-- Prove2me | Theorems.Thm_PunctSketch_products_distinct
-- name    : PunctSketch.products_distinct
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:17.906644+00:00
-- url     : https://prove2.me/theorems/c21652d4-0d07-4b70-ab3c-3cd6b65b4006
-- title:
--   Proof of Theorem 4, p.10 — the pairwise products $\alpha_i\alpha_j$ are distinct in $\mathbb F_Q$
-- statement:
--   Let $n\ge2$, let $Q>n^3$ be prime, and let $\alpha_0,\dots,\alpha_{n-1}$ be the images in $\mathbb F_Q$ of the first $n$ primes. For indices with $i\ne j$ and $i'\ne j'$,
--   $$\alpha_i\alpha_j=\alpha_{i'}\alpha_{j'}\quad\Longrightarrow\quad\{i,j\}=\{i',j'\}.$$
--   So the $\binom n2$ pairwise products are distinct, which makes the matrix $\Psi'$ of the punctured sketch a full-rank Vandermonde matrix.
--
--   Differences from the source:
--   - reading: a suitably large prime Q = Θ(n³) → any prime Q > n³, with n ≥ 2; reason: fixes the unspecified constant of Θ; the primes in (n³, 2n³], which exist by Bertrand, are of that size
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), proof of Theorem 4, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_PunctSketch_alpha

namespace PunctSketch

/-- **The pairwise products are distinct.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), proof of Theorem 4, p.10: "Importantly for us, the
(n choose 2) pairwise products α_iα_j are distinct in 𝔽_Q, since Q = Ω(n³)."

For `n ≥ 2` and a prime `Q > n³`, the map `{i, j} ↦ α_i α_j` is injective on unordered pairs of
distinct indices.

**Formalization Note.** `Q > n³` is the concrete form of `Q = Θ(n³)`. -/
theorem products_distinct {n Q : ℕ} [Fact Q.Prime] (hn : 2 ≤ n) (hQ : n ^ 3 < Q) (i j i' j' : Fin n)
    (hij : i ≠ j) (hij' : i' ≠ j') (h : alpha Q i * alpha Q j = alpha Q i' * alpha Q j') :
    s(i, j) = s(i', j') := by sorry

end PunctSketch
