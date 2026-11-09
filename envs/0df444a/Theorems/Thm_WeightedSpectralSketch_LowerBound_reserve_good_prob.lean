-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_reserve_good_prob
-- name    : WeightedSpectralSketch.LowerBound.reserve_good_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:31.878103+00:00
-- url     : https://prove2.me/theorems/a1974ca8-ec5a-4d18-922c-7c726eb1fcdf
-- title:
--   Lemma 5.3 — reserve-goodness of $x$ fails with probability at most $4N/(|R|(t+1))$
-- statement:
--   Let $b=t+s+1$, $t\ge1$, $\ell\ge2$ even, $|R|=\ell b$, and let $B$ be an incidence sketch matrix of dimension $N$ on $R$. Fix a block index $i\in\{0,\dots,\ell-1\}$. Under the uniform ring labeling, with $T_i$ given by the designated reserve slots of block $i$ and $x,y$ by the spare slots of blocks $0$ and $\ell/2$,
--
--   $$
--   \Pr\{x\text{ is not reserve-good for }T_i\text{ with respect to }y\}\le\frac{4N}{|R|(t+1)}. \tag{6}
--   $$
--
--   This makes the first representation of the query column, through the reserve $T_0$ and the root star from $y$, available with high probability.
--
--   Differences from the source:
--
--   - encoding: uniformly random permutation π placing vertices in the fixed slots → uniform distribution on bijections from the slot type to the vertex type; probabilities and conditional expectations are counting ratios; reason: a uniform permutation of [n] composed with a fixed slot numbering is a uniform bijection; same events and values
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 14, Lemma 5.3, Eq. (6), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat
import Definitions.Def_WeightedSpectralSketch_LowerBound_Reserve

open Matrix

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 5.3, p. 14, (6): for a fixed incidence sketch matrix `B` on `R`, `|R| = ℓ b`,
`b = t + s + 1`, and a fixed block index `i`, under the uniform ring labeling
`Pr{x is not reserve-good for T_i with respect to y} ≤ 4N / (|R| (t + 1))`. -/
theorem reserve_good_prob {ℓ t s : ℕ} [NeZero ℓ] (hℓ : 2 ≤ ℓ) (hℓe : Even ℓ) (ht : 0 < t)
    {R : Type*} [Fintype R] [DecidableEq R] (hR : Fintype.card R = ℓ * (t + s + 1)) {N : ℕ}
    (B : Matrix (Fin N) (EdgeSlot R) ℝ) (hB : IsIncidence B) (i : Fin ℓ) :
    prob (fun σ : Fin ℓ × Fin (t + s + 1) ≃ R => ¬ ReserveGood B σ i (spareX σ)) ≤
      4 * (N : ℝ) / ((Fintype.card R : ℝ) * (t + 1)) := by sorry

end WeightedSpectralSketch.LowerBound
