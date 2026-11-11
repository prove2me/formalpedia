-- Prove2me | Theorems.Thm_StreamingWeightedSetCover1523_LowerBound_lemma_2_1
-- name    : StreamingWeightedSetCover1523.LowerBound.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:12.329199+00:00
-- url     : https://prove2.me/theorems/dd3372a1-08e8-4bb3-9ef9-6deb78a32ef2
-- title:
--   Lemma 2.1 — repairability gives a cover of weight at most $3k$
-- statement:
--   Fix any $v,M,k$ and any $v\times M$ binary matrix $A$. Consider an outcome of the YES sampler: distinct marked indices $i\neq j$, a $k$-subset $K\subseteq[M]$, a mask $Z\in\mathbb F_2^v$ with $\Pr[Z\mid A,K]>0$ under rule (3), and NO vectors $W_1,\dots,W_M$; the YES instance keeps $V_i=W_i$ and sets $V_j=1+W_i+Z$. Then the two planted transversals together with the cheap sets indexed by $K$ form a cover of total weight at most $3k$:
--   $$T_{V_i}\cup T_{V_j}\cup\bigcup_{j'\in K}C_{j'}=U,\qquad k+k+|K|\le 3k.$$
--   No condition on $A$ is needed.
--
--   This is the YES side of the cover gap: every YES instance has a cheap completion.
--
--   Differences from the source:
--   - generalization: an outcome of the YES sampler (i* in the left block, j* in the right block), parameters satisfying (1) with k ≥ 8 → any distinct marked indices i ≠ j and arbitrary v, M, k; reason: the argument uses only i ≠ j and h(0) = 1, which hold for every k; Lemma 2.3 states the distinct-index form; it specializes to the sampler outcomes
--   - encoding: every outcome of the YES sampler → explicit elementary choices (K with |K| = k, Z with positive conditional probability, the NO vectors W before overwriting); reason: these are exactly the supported outcomes of the sampler
--   - encoding: vectors in F₂^v, a v×M binary matrix, U=[v]×{0,1}, identifiers C_1..C_M, E_1..E_M, indices 1..M → Fin v → ZMod 2, Fin v → Fin M → Bool, Fin v × ZMod 2, Fin M ⊕ Fin M, 0-based indices (left block = indices 0..r−1); reason: finite relabelling of the same objects; no instance changes
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), Lemma 2.1, printed p. 9 (PDF p. 10), eq. (7); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound

/-- Lemma 2.1 (PDF p. 10): for every matrix `A` and every outcome of the YES sampler — marked
indices `i ≠ j`, a `k`-subset `K`, a mask `Z` of positive conditional probability given `A, K`, and
the NO vectors `W` before overwriting — the planted transversals `E_i, E_j` (with `V_i = W_i`,
`V_j = 1 + W_i + Z`) together with the cheap sets indexed by `K` cover `U` at total weight at
most `3k`. No condition on `A`. -/
theorem lemma_2_1 (v M k : ℕ) (A : Mat v M) (i j : Fin M) (hij : i ≠ j)
    (K : Finset (Fin M)) (hK : K.card = k) (Z : Vec v) (hZ : maskProb k A K Z ≠ 0)
    (W : Fin M → Vec v) :
    let I := inst k A (Function.update W j (1 + W i + Z))
    let F : Finset (Ident M) := K.map Function.Embedding.inl ∪ {Sum.inr i, Sum.inr j}
    I.IsCover F ∧ I.cost F ≤ 3 * (k : ℝ) := by sorry

end StreamingWeightedSetCover1523.LowerBound
