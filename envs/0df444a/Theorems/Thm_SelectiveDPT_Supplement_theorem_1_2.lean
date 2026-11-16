-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_1_2
-- name    : SelectiveDPT.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:29:17.993199+00:00
-- url     : https://prove2.me/theorems/a0e8f628-e990-4e9e-9f06-bd3adcfe1ee3
-- title:
--   Theorem 1.2 — selective DPT for $\mathsf{SEARCH}_n$: success $\le 9\cdot2^{-2\beta k}$ with $T \le \frac{\beta}{24}k\sqrt n$
-- statement:
--   Let $0 < \beta \le 1/2$ satisfy $2^{2(\beta + H_2(\beta))/(1-\beta)} \le n$, where $H_2$ is the binary entropy (in bits). Let $k, m \ge 0$. Every quantum query algorithm for the selective direct product $\mathsf{SEARCH}_n^{(k,m)}$ that makes
--   $$T \le \frac{\beta}{24}\, k \sqrt n$$
--   queries has success probability
--   $$\Pr[\text{success}] \le 9 \cdot 2^{-2\beta k}.$$
--
--   Here the algorithm receives $m$ independent instances of $\mathsf{SEARCH}_n$ (each a string of Hamming weight one), and must output $k$ pairs $(i_j, y_j)$ with pairwise distinct copies $i_j$ of its own choice and $y_j$ the position of the $1$ in copy $i_j$. The success probability is averaged over $m$ independent uniformly random weight-one strings. So solving even $k$ self-chosen copies with fewer than order $k\sqrt n$ queries succeeds only with probability exponentially small in $k$.
--
--   Differences from the source:
--   - reading: success probability at most the bound → Σ_(x ∈ D^m) μ^m(x)·Pr[success on x] ≤ the bound, for the m-fold product of the proof's hard distribution, uniform on the weight-one strings (§4.1.1, p.26); reason: this is the quantity the proof bounds (‖Π_succ|ψ_T⟩‖² on the purified hard input); it is at least the worst-case success probability, so this is the stronger reading
--   - encoding: SEARCH_n, the function x ↦ unique i with x_i = 1 on weight-one strings → the relation x_i = 1 on the domain of weight-one strings (searchRel, searchDom); reason: on weight-one strings the relation is the graph of SEARCH_n; nothing else is read
--   - generalization: f^(k,m) for k ≤ m (Definition 1.1) → all naturals k, m; reason: for k > m no output has k distinct copies, so the success probability is 0 and the bound holds; for k ≤ m the statement is the source's
--   - encoding: inputs x ∈ {0,1}^n, m-copy inputs, a T-query phase-oracle algorithm measuring its work register and post-processing the result → bits in ZMod 2, inputs Fin n → ZMod 2, m-copy inputs on Fin m × Fin n (copy, position), QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map; reason: the base mission's conventions (§2.2, p.9 and footnote 5); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 1.2, p.4 (restated p.26)

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_prodDist
import Definitions.Def_SelectiveDPT_selRel
import Definitions.Def_SelectiveDPT_H2
import Definitions.Def_SelectiveDPT_Supplement_searchDom

namespace SelectiveDPT.Supplement

open QAlgorithms

/-- Theorem 1.2 of Beame–Kornerup–Whitmeyer, arXiv:2609.26678, p.4 (restated p.26): let
`0 < β ≤ 1/2` be such that `2^{2(β + H₂(β))/(1−β)} ≤ n`. Every quantum query algorithm solving
`SEARCH_n^(k,m)` with `T ≤ (β/24) k √n` queries has success probability at most `9 · 2^{−2βk}`.

**Formalization Note.** The success probability is the average over the paper's hard
distribution, `m` independent copies of the uniform distribution on the weight-`1` strings
(§4.1.1, p.26): `Σ_{x ∈ D^m} μ^m(x) · Pr[A succeeds on x]`. This bounds the worst case too. The
algorithm is any `T`-query phase-oracle algorithm (base `QueryAlg`, any workspace `Fin b`, any
post-processing `out`) whose output is `k` (copy, index) pairs with distinct copies, checked by
the base `selRel`. `k` and `m` are arbitrary; for `k > m` no output is correct. -/
theorem theorem_1_2 (n : ℕ) (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β ≤ 1 / 2)
    (hn : (2 : ℝ) ^ (2 * (β + H2 β) / (1 - β)) ≤ n) (k m b T : ℕ)
    (A : QueryAlg (Fin m × Fin n) (ZMod 2) (Fin b) T)
    (out : ((Fin m × Fin n) × ZMod 2) × Fin b → (Fin k → Fin m × Fin n))
    (hT : (T : ℝ) ≤ β / 24 * k * Real.sqrt n) :
    ∑ x ∈ prodDomain (searchDom n) m,
        prodDist (searchDist n) m x * successProb A out (selRel k m (searchRel n)) x ≤
      9 * (2 : ℝ) ^ (-(2 * β * k)) := by sorry

end SelectiveDPT.Supplement
