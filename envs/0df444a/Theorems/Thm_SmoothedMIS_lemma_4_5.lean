-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_4_5
-- name    : SmoothedMIS.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:21.523295+00:00
-- url     : https://prove2.me/theorems/e72251ed-07a9-46ac-a959-226b6bc24671
-- title:
--   Lemma 4.5 — condition (1) holds w.h.p. for every base graph
-- statement:
--   Fix $c>0$, any constant $a\ge48(c+3)$, and put $\beta=2a$, so that $\lambda=2a\ln n$ and $k=\lceil a\ln n\rceil$ (the parameters of the analysis, §4.2). There is $n_0$, depending only on $c$ and $a$, such that for every $n\ge n_0$ and every base graph $G$ on $n$ vertices, condition (1) holds with probability at least $1-n^{-c-1}$.
--
--   The probability is over the random edges and the marks of Step 1. It combines the case $M=0$ with Lemmas 4.7, 4.8 and 4.13, and feeds Lemma 4.4 in the proof of Theorem 4.1.
--
--   **Formalization Note** The base-graph quantities $M,z_H,t,z_Q$ are those of §4.2.1 and are compared as real numbers.
--
--   Differences from the source:
--   - reading: for all sufficiently large n → ∃ n0 depending only on c and a, before the base graph G; reason: the proof's thresholds involve only n, c and a (Theorem 4.1 needs this uniformity in G)
--   - encoding: a ≥ 48(c + 3) a constant and q ≥ 2c + 7 an integer (p.20) → every a ≥ 48(c + 3); q not in the statement; reason: q is used only inside the proof (Lemma 4.10), and the statement does not mention it
--   - encoding: the probabilities over the random edges R and the marks of Step 1 → the analysis law: smoothing coins on all pairs with probability min(1, β ln n/n) and independent mark coins κ_uv on all pairs with probability θ (clamped to [0,1]); reason: p.25 states that the per-pair coins have the same distribution as the algorithm; coins on edges of G change nothing; the clamps are the identity for large n
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 4.5, p.20; proof §4.2.1, pp.20–28 (PDF pp.22–30)

import Mathlib
import Definitions.Def_SmoothedMIS_testSet

open MeasureTheory

namespace SmoothedMIS

/-- **Lemma 4.5** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for Distributed
MIS* (manuscript, sha256 dc2131db…), Lemma 4.5, p.20). For every base graph `G` and all sufficiently large `n`,
condition (1) holds with probability at least `1 − n^{−c−1}`.

**Formalization Note** The parameters of the analysis (§4.2, p.20): `c > 0`, any constant
`a ≥ 48(c + 3)`, `β = 2a` (so `λ = 2a ln n`), `k = ⌈a ln n⌉`. The probability is over the
analysis law `anaLaw n β` (smoothing coins and the mark coins `κ` of p.25). `n0` depends on
`c` and `a` only, not on the base graph `G : SimpleGraph (Fin n)`. All base-graph quantities
(`M, z_H, t, z_Q`) are those of §4.2.1 and are compared as reals. -/
theorem lemma_4_5 : ∀ c : ℝ, 0 < c → ∀ a : ℝ, 48 * (c + 3) ≤ a → ∃ n0 : ℕ, ∀ n ≥ n0,
    ∀ G : SimpleGraph (Fin n),
      1 - (n : ℝ) ^ (-c - 1) ≤ (anaLaw n (2 * a) {ω | cond1 (2 * a) G ω}).toReal := by sorry

end SmoothedMIS
