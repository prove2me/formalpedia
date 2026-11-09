-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_expected_incidence_dim
-- name    : WeightedSpectralSketch.LowerBound.expected_incidence_dim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:53.989206+00:00
-- url     : https://prove2.me/theorems/fd9246b5-b228-43c5-b37e-20af21f05347
-- title:
--   Lemma 6.5 — expected incidence dimension $\mathbb E_C[K(C)]\le4N$
-- statement:
--   Let $|V|=2\ell b$ and let $A$ be any fixed real sketch matrix with $N$ rows. If the anchor $C$ is uniform among the subsets of $V$ of size $\ell b$, then
--
--   $$
--   \mathbb E_C\big[K(C)\big]\le4N,\qquad K(C)=\sum_{v\in V\setminus C}n_+\big(A_{v,C}A_{v,C}^\top-A_CA_C^\top\big).
--   $$
--
--   $K(C)$ is the dimension of the incidence sketch built in Lemma 6.3, so this keeps the reduced incidence sketch within a constant factor of the original dimension in expectation. No rank, nonsingularity or concentration condition on $A$ is assumed.
--
--   Differences from the source:
--
--   - encoding: E_C over a uniform half-size anchor set → the average of K(C) over all subsets of size ℓb; reason: uniform expectation over a finite set
--   - generalization: the anchored template of §6.1 (b ≥ 2, ℓ ≥ 2 even, vertex set [n], n = 2ℓb) → any natural numbers ℓ, b and any finite vertex type of cardinality 2ℓb; reason: the source's setting is the instance b ≥ 2, ℓ ≥ 2 even; the statement does not involve the ring blocks or the query edge
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 24, Lemma 6.5 (K(C) defined p. 23), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Anchor

open Matrix

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 6.5, p. 24: for any fixed sketch matrix `A`, with `C` uniform among the subsets of size
`ℓ b` of the `2 ℓ b` vertices, `E_C[K(C)] ≤ 4N`. -/
theorem expected_incidence_dim {ℓ b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 2 * (ℓ * b)) {N : ℕ} (A : Matrix (Fin N) (EdgeSlot V) ℝ) :
    (∑ C ∈ Finset.powersetCard (ℓ * b) (Finset.univ : Finset V), (KDim A C : ℝ)) /
        (Finset.powersetCard (ℓ * b) (Finset.univ : Finset V)).card ≤ 4 * N := by sorry

end WeightedSpectralSketch.LowerBound
