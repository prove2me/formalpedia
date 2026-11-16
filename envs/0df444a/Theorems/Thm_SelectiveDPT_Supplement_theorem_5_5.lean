-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_5_5
-- name    : SelectiveDPT.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:36:05.800464+00:00
-- url     : https://prove2.me/theorems/72ef93aa-c20b-4312-9c93-f72b5f035b3d
-- title:
--   Theorem 5.5 (corrected: $n\ge2$) — list-decoding DPT for $\mathsf{SEARCH}_n$: success $\le 9\cdot2^{-k/4}$ with $k\sqrt n/192$ queries
-- statement:
--   Let $n \ge 2$ and $k, m \ge 0$. Every quantum algorithm for the list-decoding direct product $\mathsf{SEARCH}_n^{L(k,m)}$ making at most
--   $$\frac{k\sqrt n}{192}$$
--   queries has success probability
--   $$\Pr[\text{success}] \le 9 \cdot 2^{-k/4}.$$
--
--   The algorithm outputs a list of at most $n^{m-k}$ vectors in $[n]^m$ and succeeds when the list contains the positions of the $1$s of all $m$ inputs; the success probability is averaged over $m$ independent uniformly random weight-one strings.
--
--   Differences from the source:
--   - correction: SEARCH_n for every n → n ≥ 2; reason: the proof uses n ≥ 2 (p.45); at n = 1 SEARCH_1 has one answer, so the one-element list is always correct with 0 queries, and 1 > 9 · 2^{−13/4} at k = m = 13
--   - reading: success probability at most the bound → Σ_(x ∈ D^m) μ^m(x)·Pr[success on x] ≤ the bound, for the m-fold product of the proof's hard distribution, uniform on the weight-one strings (§4.1.1, p.26); reason: this is the quantity the proof bounds (‖Π_succ|ψ_T⟩‖² on the purified hard input); it is at least the worst-case success probability, so this is the stronger reading
--   - generalization: L ∈ (Y^m choose |Y|^{m−k}) (Definition 5.1, lists of exactly |Y|^{m−k} vectors) → lists L ⊆ Y^m with |L|·|Y|^k ≤ |Y|^m (listRel); reason: every list of the exact size qualifies, so the Lean statement covers the source's; the size 'at most |Y|^{m−k}' is the one of the introduction (p.6) and of the proofs (p.46)
--   - encoding: SEARCH_n, the function x ↦ unique i with x_i = 1 on weight-one strings → the relation x_i = 1 on the domain of weight-one strings (searchRel, searchDom); reason: on weight-one strings the relation is the graph of SEARCH_n; nothing else is read
--   - generalization: f^{L(k,m)} for k ≤ m → all naturals k, m; reason: for k > m and |Y| ≥ 2 only the empty list meets the size bound and it is never correct, so the bound holds; for k ≤ m the statement is the source's
--   - encoding: inputs x ∈ {0,1}^n, m-copy inputs, a T-query phase-oracle algorithm measuring its work register and post-processing the result → bits in ZMod 2, inputs Fin n → ZMod 2, m-copy inputs on Fin m × Fin n (copy, position), QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map; reason: the base mission's conventions (§2.2, p.9 and footnote 5); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 5.5, p.44

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_prodDist
import Definitions.Def_SelectiveDPT_Supplement_searchDom
import Definitions.Def_SelectiveDPT_Supplement_listRel

namespace SelectiveDPT.Supplement

open QAlgorithms

/-- Theorem 5.5 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.44: any quantum algorithm for
`SEARCH_n^{L(k,m)}` with at most `k√n/192` queries has success probability at most `9 · 2^{−k/4}`.

**Formalization Note.** The success probability is the average over `m` independent copies of
the uniform distribution on the weight-`1` strings (§4.1.1). The output is a list of at most
`n^{m−k}` vectors in `[n]^m` (`listRel`, `|Y| = n`). `k`, `m` arbitrary. **Correction:** `n ≥ 2`,
which the proof uses ("since `n ≥ 2`", p.45): at `n = 1`, `SEARCH_1` has a single answer, so the
one-element list is always correct with `0` queries, and `1 > 9 · 2^{−13/4}` at `k = m = 13`. -/
theorem theorem_5_5 (n : ℕ) (hn : 2 ≤ n) (k m b T : ℕ)
    (A : QueryAlg (Fin m × Fin n) (ZMod 2) (Fin b) T)
    (out : ((Fin m × Fin n) × ZMod 2) × Fin b → Finset (Fin m → Fin n))
    (hT : (T : ℝ) ≤ k * Real.sqrt n / 192) :
    ∑ x ∈ prodDomain (searchDom n) m,
        prodDist (searchDist n) m x * successProb A out (listRel k m (searchRel n)) x ≤
      9 * (2 : ℝ) ^ (-(k : ℝ) / 4) := by sorry

end SelectiveDPT.Supplement
