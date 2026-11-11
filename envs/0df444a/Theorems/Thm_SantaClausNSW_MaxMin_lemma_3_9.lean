-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_lemma_3_9
-- name    : SantaClausNSW.MaxMin.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:35:12.576949+00:00
-- url     : https://prove2.me/theorems/71beebb7-d430-4f61-a6a9-624800808ec3
-- title:
--   Lemma 3.9 — independent sampling at rate ≥ 1/h keeps value W/(4h) with probability ≥ 1/2
-- statement:
--   Let $v$ be a normalized monotone subadditive valuation and let $S$ satisfy $v(S)=W>0$. Fix an integer $h\ge1$ with $v(\{j\})\le W/(8h)$ for every $j\in S$. If $Q\subseteq S$ is obtained by retaining each item independently with probability at least $1/h$, then
--   $$\Pr\Big[v(Q)\ge\frac{W}{4h}\Big]\ge\frac12 .$$
--   Lemma 3.11 applies it to the random coloring of the items.
--
--   Differences from the source:
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: retaining each item independently with probability at least 1/h → retention probabilities p_j ∈ [1/h, 1] (j ∈ S) and the product law Pr[Q] = ∏_{j∈Q} p_j ∏_{j∈S∖Q} (1 − p_j); reason: p_j ≤ 1 only says p_j is a probability; the product law is independent retention
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 25, Lemma 3.9

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Valuations

namespace SantaClausNSW.MaxMin

/-- **Lemma 3.9** (p. 25). Let `v` be a normalized monotone subadditive valuation and `S` a set
with `v(S) = W > 0`. Fix an integer `h ≥ 1` with `v({j}) ≤ W/(8h)` for every `j ∈ S`. If `Q ⊆ S`
retains each item `j` independently with probability `p_j ≥ 1/h`, then
`Pr[v(Q) ≥ W/(4h)] ≥ 1/2`. -/
theorem lemma_3_9 {m : ℕ} (v : Finset (Fin m) → ℝ) (hv : IsValuation v)
    (hsub : IsSubadditive v) (S : Finset (Fin m)) (W : ℝ) (hW : v S = W) (hW0 : 0 < W)
    (h : ℕ) (hh : 1 ≤ h) (hsing : ∀ j ∈ S, v {j} ≤ W / (8 * h))
    (p : Fin m → ℝ) (hp : ∀ j ∈ S, 1 / (h : ℝ) ≤ p j ∧ p j ≤ 1) :
    1 / 2 ≤ retainProb S p (fun Q => W / (4 * h) ≤ v Q) := by sorry

end SantaClausNSW.MaxMin
