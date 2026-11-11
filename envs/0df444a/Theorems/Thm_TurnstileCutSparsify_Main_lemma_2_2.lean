-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_lemma_2_2
-- name    : TurnstileCutSparsify.Main.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:39:09.036576+00:00
-- url     : https://prove2.me/theorems/d6811bad-d5b0-474b-a790-6105dd3243df
-- title:
--   Lemma 2.2 — Σ_{e∈E} w_e/λ_e ≤ n − 1 ([FHHP19, Corollary 1.7])
-- statement:
--   For a graph $G=(V,E,w)$ on $n\ge2$ vertices with nonnegative integer weights, $E=\{e:w_e>0\}$ and connectivities $\lambda_e$ (1),
--   $$\sum_{e\in E}\frac{w_e}{\lambda_e}\le n-1 .$$
--   Cited from [FHHP19, Corollary 1.7]; it bounds the expected output size (33) of the sparsifier.
--
--   Differences from the source:
--   - encoding: vertices V = [n]; coordinates = the N unordered pairs; graphs G = (V, E, w) → vertices Fin n (0-based); Pair n = {(u, v) : u < v}; a graph is a weight function on Pair n (E = pairs of positive weight); reason: same graphs; the canonical pair order is not needed by the statement
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Lemma 2.2, p. 10

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph

open scoped BigOperators Classical

namespace TurnstileCutSparsify.Main

/-- **Lemma 2.2** ([FHHP19, Corollary 1.7]; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 10).
For a graph on `n ≥ 2` vertices with nonnegative integer weights `w`,
`Σ_{e ∈ E} w_e / λ_e ≤ n − 1`, where `E = {e : w_e > 0}` and `λ_e` is the connectivity (1). -/
theorem lemma_2_2 (n : ℕ) (hn : 2 ≤ n) (w : Pair n → ℕ) :
    ∑ e ∈ Finset.univ.filter (fun e => 0 < w e), (w e : ℝ) / conn (toR w) e ≤ (n : ℝ) - 1 := by sorry

end TurnstileCutSparsify.Main
