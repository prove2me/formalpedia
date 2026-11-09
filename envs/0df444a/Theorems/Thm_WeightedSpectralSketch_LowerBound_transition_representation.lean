-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_transition_representation
-- name    : WeightedSpectralSketch.LowerBound.transition_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:39.335196+00:00
-- url     : https://prove2.me/theorems/e3d32083-ac7a-4899-83f5-a517f73d0f09
-- title:
--   Lemma 5.4 — telescoping root-star transition representation
-- statement:
--   Let $b=t+s+1$, $t\ge1$, $\ell\ge2$ even, $|R|=\ell b$, and let $B$ be an incidence sketch matrix of dimension $N$ on $R$. Fix distinct block indices $i,j$ and consider $T_i,T_j,S_i$. Under the uniform ring labeling, with probability at least
--
--   $$
--   1-\frac{8N}{|R|(t+1)}-\frac{4t}{s+1},
--   $$
--
--   1. $x$ is reserve-good for both $T_i$ and $T_j$, and
--   2. there are coefficients $f=(f_e)_{e\in\binom R2\setminus\{q\}}$ with
--   $$B_{y,T_i}\alpha^{(x)}_{y,T_i}-B_{y,T_j}\alpha^{(x)}_{y,T_j}=\sum_{e\ne q}f_eb_e,\qquad \mathrm{supp}(f)\subseteq\tbinom{T_i}2\cup\tbinom{T_j}2\cup\{uv:u\in S_i,\ v\in T_i\cup T_j\},$$
--   $$\sum_{u\in S_i}\sum_{v\in T_j}f_{uv}^2\le1, \tag{9}$$
--   $$\sum_{e\in\binom{T_i}2\cup\binom{T_j}2}f_e^2+\sum_{u\in S_i}\sum_{v\in T_i}f_{uv}^2\le2s+1. \tag{10}$$
--
--   Only the coefficients between $S_i$ and $T_j$ cross blocks, and (9) bounds their squared sum by one: this is the cost of one transition in the routing of Lemma 5.5.
--
--   **Formalization Note.** The root-star terms are those of the definition `rootStar` (minimum-norm coefficients of (7)); they are the source's terms on the event of clause 1.
--
--   Differences from the source:
--
--   - encoding: uniformly random permutation π placing vertices in the fixed slots → uniform distribution on bijections from the slot type to the vertex type; probabilities and conditional expectations are counting ratios; reason: a uniform permutation of [n] composed with a fixed slot numbering is a uniform bijection; same events and values
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, pp. 15–16, Lemma 5.4, Eqs. (9)–(10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat
import Definitions.Def_WeightedSpectralSketch_LowerBound_Reserve

open Matrix

namespace WeightedSpectralSketch.LowerBound

open Classical in
/-- Lemma 5.4, pp. 15–16: for distinct block indices `i, j`, with probability at least
`1 - 8N/(|R|(t+1)) - 4t/(s+1)` under the uniform ring labeling, (1) `x` is reserve-good for `T_i`
and `T_j`, and (2) the difference of the root-star terms of `x` is `∑_{e ≠ q} f_e b_e` for some `f`
supported on `binom(T_i,2) ∪ binom(T_j,2) ∪ {uv : u ∈ S_i, v ∈ T_i ∪ T_j}` with
`∑_{u ∈ S_i, v ∈ T_j} f_{uv}² ≤ 1` (9) and
`∑_{e ∈ binom(T_i,2) ∪ binom(T_j,2)} f_e² + ∑_{u ∈ S_i, v ∈ T_i} f_{uv}² ≤ 2s + 1` (10). -/
theorem transition_representation {ℓ t s : ℕ} [NeZero ℓ] (hℓ : 2 ≤ ℓ) (hℓe : Even ℓ) (ht : 0 < t)
    {R : Type*} [Fintype R] [DecidableEq R] (hR : Fintype.card R = ℓ * (t + s + 1)) {N : ℕ}
    (B : Matrix (Fin N) (EdgeSlot R) ℝ) (hB : IsIncidence B) (i j : Fin ℓ) (hij : i ≠ j) :
    1 - 8 * (N : ℝ) / ((Fintype.card R : ℝ) * (t + 1)) - 4 * (t : ℝ) / (s + 1) ≤
      prob (fun σ : Fin ℓ × Fin (t + s + 1) ≃ R =>
        ReserveGood B σ i (spareX σ) ∧ ReserveGood B σ j (spareX σ) ∧
        ∃ f : {e : EdgeSlot R // e.1 ≠ querySym σ} → ℝ,
          rootStar B σ i (spareX σ) - rootStar B σ j (spareX σ) = ∑ e, f e • Bᵀ e.1 ∧
          (∀ e, f e ≠ 0 → IsWithin (reserveSet σ i) e.1 ∨ IsWithin (reserveSet σ j) e.1 ∨
            IsBetween (auxSet σ i) (reserveSet σ i ∪ reserveSet σ j) e.1) ∧
          (∑ e, if IsBetween (auxSet σ i) (reserveSet σ j) e.1 then f e ^ 2 else 0) ≤ 1 ∧
          (∑ e, if IsWithin (reserveSet σ i) e.1 ∨ IsWithin (reserveSet σ j) e.1
              then f e ^ 2 else 0) +
            (∑ e, if IsBetween (auxSet σ i) (reserveSet σ i) e.1 then f e ^ 2 else 0) ≤
            2 * (s : ℝ) + 1) := by sorry

end WeightedSpectralSketch.LowerBound
