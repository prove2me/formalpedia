-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_anchor_good_prob
-- name    : WeightedSpectralSketch.LowerBound.anchor_good_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:13:17.918204+00:00
-- url     : https://prove2.me/theorems/567adda0-ef97-4e23-b0b3-474fa45b85f8
-- title:
--   Lemma 6.2 — the query edge is anchor-good with high probability
-- statement:
--   Fix $b\ge2$, $\ell\ge2$ even, $|V|=2\ell b$, and any real sketch matrix $A$ with $N$ rows. Under the uniform anchored labeling $\pi$, with anchor $C$ and query edge $q$,
--
--   $$
--   \Pr_\pi\{q\text{ is not anchor-good}\}\le2N\Big/\binom{\ell b+2}{2}. \tag{14}
--   $$
--
--   Anchor-goodness of $q$ is the hypothesis of the lifting Lemma 6.4; this bound makes its failure negligible in the final leverage estimate.
--
--   Differences from the source:
--
--   - encoding: uniformly random permutation π placing vertices in the fixed slots → uniform distribution on bijections from the slot type to the vertex type; probabilities and conditional expectations are counting ratios; reason: a uniform permutation of [n] composed with a fixed slot numbering is a uniform bijection; same events and values
--   - encoding: the distinguished query slots of Section 4 → arbitrary fixed positions j_x, j_y in blocks 0 and ℓ/2; reason: Section 4 fixes them arbitrarily
--   - encoding: vertex set [n], n = 2ℓb → any finite vertex type of cardinality 2ℓb; reason: relabelling vertices changes nothing
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 23, Lemma 6.2, Eq. (14), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat
import Definitions.Def_WeightedSpectralSketch_LowerBound_Anchor

open Matrix

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 6.2, p. 23, (14): for any fixed sketch matrix `A`, under the uniform anchored labeling
`π`, `Pr_π{q is not anchor-good} ≤ 2N / binom(ℓb + 2, 2)`. -/
theorem anchor_good_prob {ℓ b : ℕ} [NeZero ℓ] (hb : 2 ≤ b) (hℓ : 2 ≤ ℓ) (hℓe : Even ℓ)
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2 * (ℓ * b)) (jx jy : Fin b)
    {N : ℕ} (A : Matrix (Fin N) (EdgeSlot V) ℝ) :
    prob (fun π : AnchSlot ℓ b ≃ V => ¬ AnchorGood A (anchorSet π) (anchQuery π jx jy)) ≤
      2 * (N : ℝ) / ((ℓ * b + 2).choose 2 : ℕ) := by sorry

end WeightedSpectralSketch.LowerBound
