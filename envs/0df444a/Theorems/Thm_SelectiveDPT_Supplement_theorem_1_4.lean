-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_1_4
-- name    : SelectiveDPT.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:30:16.519086+00:00
-- url     : https://prove2.me/theorems/1ebbcc86-a650-4c29-a7e8-d15d6489bb46
-- title:
--   Theorem 1.4 — selective DPT for $\mathsf{OR}_n$: success $\le 9\cdot2^{-2\beta k}$ with $T \le \frac{\beta}{16}k\sqrt n$
-- statement:
--   Let $\beta > 0$ satisfy $3\beta + 2H_2(\beta) \le 1$, let $n \ge 1$ and $k, m \ge 0$. Every quantum query algorithm for the selective direct product $\mathsf{OR}_n^{(k,m)}$ that makes
--   $$T \le \frac{\beta}{16}\, k \sqrt n$$
--   queries has success probability
--   $$\Pr[\text{success}] \le 9 \cdot 2^{-2\beta k}.$$
--
--   The algorithm outputs $k$ pairs (copy, bit) with pairwise distinct copies of its choice, and succeeds when every bit is the $\mathsf{OR}$ of its copy. The success probability is averaged over $m$ independent inputs from the hard distribution of $\mathsf{OR}_n$ ($1/2$ on $0^n$, $1/(2n)$ on each weight-one string). By Remark 1.5 the condition on $\beta$ holds for every $0 < \beta \le 0.07562$.
--
--   Differences from the source:
--   - reading: success probability at most the bound → Σ_(x ∈ D^m) μ^m(x)·Pr[success on x] ≤ the bound, for the m-fold product of the proof's hard distribution, 1/2 on 0^n and 1/(2n) on each weight-one string (§4.1.2, p.30); reason: this is the quantity the proof bounds (‖Π_succ|ψ_T⟩‖² on the purified hard input); it is at least the worst-case success probability, so this is the stronger reading
--   - encoding: n arbitrary → 0 < n; reason: at n = 0 no query algorithm exists (the query register Fin m × Fin 0 is empty), so the statement would be vacuous; the hard distribution is also undefined there
--   - generalization: f^(k,m) for k ≤ m (Definition 1.1) → all naturals k, m; reason: for k > m no output has k distinct copies, so the success probability is 0 and the bound holds; for k ≤ m the statement is the source's
--   - encoding: inputs x ∈ {0,1}^n, m-copy inputs, a T-query phase-oracle algorithm measuring its work register and post-processing the result → bits in ZMod 2, inputs Fin n → ZMod 2, m-copy inputs on Fin m × Fin n (copy, position), QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map; reason: the base mission's conventions (§2.2, p.9 and footnote 5); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 1.4, p.4 (restated p.30)

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_prodDist
import Definitions.Def_SelectiveDPT_selRel
import Definitions.Def_SelectiveDPT_H2
import Definitions.Def_SelectiveDPT_Supplement_orFn

namespace SelectiveDPT.Supplement

open QAlgorithms

/-- Theorem 1.4 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.4 (restated p.30): let
`0 < β` be such that `3β + 2H₂(β) ≤ 1`. Every quantum query algorithm solving `OR_n^(k,m)` with
`T ≤ (β/16) k √n` queries has success probability at most `9 · 2^{−2βk}`.

**Formalization Note.** The success probability is the average over `m` independent copies of
the paper's hard distribution for `OR_n` (§4.1.2, p.30: `1/2` on `0^n`, `1/(2n)` on each weight-`1`
string); the domain is all of `{0,1}^n`. `0 < n`: at `n = 0` that distribution is not a
probability distribution, and no query algorithm exists (empty query register). Outputs are `k`
(copy, bit) pairs with distinct copies (base `selRel`). -/
theorem theorem_1_4 (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ₀ : 0 < β) (hβ : 3 * β + 2 * H2 β ≤ 1)
    (k m b T : ℕ) (A : QueryAlg (Fin m × Fin n) (ZMod 2) (Fin b) T)
    (out : ((Fin m × Fin n) × ZMod 2) × Fin b → (Fin k → Fin m × ZMod 2))
    (hT : (T : ℝ) ≤ β / 16 * k * Real.sqrt n) :
    ∑ x ∈ prodDomain (Finset.univ : Finset (Fin n → ZMod 2)) m,
        prodDist (orDist n) m x * successProb A out (selRel k m (fun x y => orFn n x = y)) x ≤
      9 * (2 : ℝ) ^ (-(2 * β * k)) := by sorry

end SelectiveDPT.Supplement
