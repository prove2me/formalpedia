-- Prove2me | Theorems.Thm_SoftmaxAttnFD_lemma_6_9
-- name    : SoftmaxAttnFD.lemma_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:24.569305+00:00
-- url     : https://prove2.me/theorems/7bff27c3-0849-4ab1-bc9b-e1dc9d9263d8
-- title:
--   Lemma 6.9, p.25 — sampling bound on conflict sets
-- statement:
--   Let $d\ge3$. There is $C_{\rm samp}>0$ depending only on $d$ such that for every capped family with $|\Sigma_0|\le N$, $N\ge1$, with $G=\lceil\log_2(N+8)\rceil$, every $\emptyset\ne\Sigma\subseteq\Sigma_0$ and every size $1\le|\Sigma'|\le|\Sigma|$: for a uniformly random subset $\Sigma'$ of $\Sigma$ of that size, with probability at least $1-1/(8G)$, every canonical cell of $P(\Sigma')$ satisfies
--   $$|C_\Delta|\le C_{\rm samp}\frac{|\Sigma|\,G}{|\Sigma'|},$$
--   with conflict sets relative to $\Sigma$.
--
--   Differences from the source:
--   - generalization: the concrete family of Definition 6.4 → any capped family; reason: the statement uses only the capped-family properties, and Lemma 6.5 shows the concrete family is capped
--   - encoding: "with probability at least 1 − 1/(8G)" for a uniformly random subset → 8G · #(bad samples) ≤ #(all samples of that size), over powersetCard; reason: a uniform probability on a finite set is this ratio
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Lemma 6.9, p.25; (6.1), p.25

import Definitions.Def_SoftmaxAttnFD_CanonicalCells

namespace SoftmaxAttnFD

open Classical in
/-- **Lemma 6.9** (arXiv:2611.06055, sha256 a60f7609…, p.25), on any capped family, with
`G = ⌈log₂(N + 8)⌉` from (6.1). With probability at least `1 − 1/(8G)` over a uniformly random subset
`Σ′` of `Σ` of the given size, every canonical cell has `|C_∆| ≤ C_samp |Σ| G/|Σ′|`.

**Formalization Note** The probability is a count over `Finset.powersetCard`: the fraction of bad
samples is at most `1/(8G)`. `C_samp` depends only on `d`, before the family. The conflict sets are
subsets of `Σ`, so `ncard` is their cardinality. Lemma 6.5 shows the concrete family of Definition 6.4
is capped, so this specializes to the page's statement. -/
theorem lemma_6_9 (d : ℕ) (hd : 3 ≤ d) :
    ∃ Csamp : ℝ, 0 < Csamp ∧
      ∀ (F : Family d) (S₀ : Finset ℕ) (U N : ℕ), 1 ≤ N → IsCappedFamily F S₀ U → S₀.card ≤ N →
      ∀ (S : Finset ℕ) (size : ℕ), S.Nonempty → S ⊆ S₀ → 1 ≤ size → size ≤ S.card →
        8 * ⌈Real.logb 2 ((N : ℝ) + 8)⌉₊ *
            ((Finset.powersetCard size S).filter fun S' =>
              ∃ (s : ℕ) (vs : Fin d → Fin (d - 1) → ℝ), F.IsCanonicalCell S' s vs ∧
                Csamp * S.card * ⌈Real.logb 2 ((N : ℝ) + 8)⌉₊ / size <
                  ((F.conflictSet S s vs).ncard : ℝ)).card ≤
          (Finset.powersetCard size S).card := by sorry

end SoftmaxAttnFD
