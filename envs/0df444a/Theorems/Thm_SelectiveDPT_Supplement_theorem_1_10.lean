-- Prove2me | Theorems.Thm_SelectiveDPT_Supplement_theorem_1_10
-- name    : SelectiveDPT.Supplement.theorem_1_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:31:35.26794+00:00
-- url     : https://prove2.me/theorems/d2fb67a0-a6e9-4c80-a8ac-e6d5f554fece
-- title:
--   Theorem 1.10 (corrected: $n \ge 2$ for $\mathsf{SEARCH}_n$) — list-decoding DPTs for $\mathsf{SEARCH}_n$, $\mathsf{OR}_n$, $\mathsf{PARITY}_n$
-- statement:
--   There are constants $c, c'' > 0$ such that for all $n$ and all integers $1 \le k \le m$:
--   1. if $n \ge 2$, every quantum algorithm for the list-decoding direct product $\mathsf{SEARCH}_n^{L(k,m)}$ making at most $ck\sqrt n$ queries succeeds with probability at most $2^{-c''k}$;
--   2. if $n \ge 1$, every quantum algorithm for $\mathsf{OR}_n^{L(k,m)}$ making at most $ck\sqrt n$ queries succeeds with probability at most $2^{-c''k}$;
--   3. if $n \ge 1$, every quantum algorithm for $\mathsf{PARITY}_n^{L(k,m)}$ making at most $ckn$ queries succeeds with probability at most $2^{-c''k}$.
--
--   In the list-decoding problem the algorithm outputs a list of at most $|Y|^{m-k}$ vectors in $Y^m$ ($|Y| = n$ for $\mathsf{SEARCH}_n$, $|Y| = 2$ otherwise), and succeeds when the list contains the vector of all $m$ correct answers. Success probabilities are averaged over $m$ independent inputs from the hard distribution of each problem. This is stronger than the selective theorems, since a selective output is a special list.
--
--   Differences from the source:
--   - correction: (i) SEARCH_n for every n → (i) for n ≥ 2; reason: at n = 1, SEARCH_1 has the single answer 1, so the one-element list is always correct with 0 queries and the success probability 1 exceeds 2^{−c''k} for every c'' > 0 and k ≥ 1; the proof of Theorem 5.5 uses n ≥ 2 (p.45)
--   - encoding: (ii), (iii) for every n → (ii), (iii) for n ≥ 1; reason: at n = 0 no query algorithm exists (empty query register) and the OR_0 hard distribution is undefined
--   - reading: there are constants c, c'' > 0 such that for every positive integer k ≤ m, (i) or (ii) or (iii) → one pair (c, c'') chosen before n, k, m serving all three problems; reason: the sentence fixes c and c'' before the problem and its size
--   - reading: success probability at most the bound → Σ_(x ∈ D^m) μ^m(x)·Pr[success on x] ≤ the bound, for the m-fold product of each problem's hard distribution (uniform on weight-one strings for SEARCH_n; 1/2 on 0^n and 1/(2n) on weight-one strings for OR_n; uniform for PARITY_n); reason: this is the quantity the proof bounds (‖Π_succ|ψ_T⟩‖² on the purified hard input); it is at least the worst-case success probability, so this is the stronger reading
--   - generalization: L ∈ (Y^m choose |Y|^{m−k}) (Definition 5.1, lists of exactly |Y|^{m−k} vectors) → lists L ⊆ Y^m with |L|·|Y|^k ≤ |Y|^m (listRel); reason: every list of the exact size qualifies, so the Lean statement covers the source's; the size 'at most |Y|^{m−k}' is the one of the introduction (p.6) and of the proofs (p.46)
--   - encoding: SEARCH_n, the function x ↦ unique i with x_i = 1 on weight-one strings → the relation x_i = 1 on the domain of weight-one strings (searchRel, searchDom); reason: on weight-one strings the relation is the graph of SEARCH_n; nothing else is read
--   - encoding: inputs x ∈ {0,1}^n, m-copy inputs, a T-query phase-oracle algorithm measuring its work register and post-processing the result → bits in ZMod 2, inputs Fin n → ZMod 2, m-copy inputs on Fin m × Fin n (copy, position), QAlgorithms.QueryAlg with workspace Fin b for any b, a full computational-basis measurement followed by an output map; reason: the base mission's conventions (§2.2, p.9 and footnote 5); only the workspace dimension matters; measuring a designated output register is a special output map
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Theorem 1.10, p.6

import Mathlib
import Definitions.Def_SelectiveDPT_Qrel
import Definitions.Def_SelectiveDPT_prodDomain
import Definitions.Def_SelectiveDPT_prodDist
import Definitions.Def_SelectiveDPT_Supplement_searchDom
import Definitions.Def_SelectiveDPT_Supplement_orFn
import Definitions.Def_SelectiveDPT_Supplement_parityFn
import Definitions.Def_SelectiveDPT_Supplement_listRel

namespace SelectiveDPT.Supplement

open QAlgorithms

/-- Theorem 1.10 of arXiv:2609.26678 (Beame–Kornerup–Whitmeyer), p.6: there are constants
`c, c″ > 0` such that for every positive integer `k ≤ m`, any quantum algorithm solving the
list-decoding direct-product problem with parameter `k` for either (i) `SEARCH_n` or (ii) `OR_n`
making at most `c k √n` queries, or (iii) `PARITY_n` making at most `c k n` queries has success
probability at most `2^{−c″k}`.

**Formalization Note.** One pair `(c, c″)` is chosen before `n`, `k`, `m` and serves all three
problems. Success probabilities are averages over `m` independent copies of the paper's hard
distributions (uniform on weight-`1` strings for `SEARCH_n`, §4.1.1; `1/2` on `0^n` and `1/(2n)` on
each weight-`1` string for `OR_n`, §4.1.2; uniform for `PARITY_n`, p.32). The list-decoding output is
a list of at most `|Y|^{m−k}` answer vectors (`listRel`), `|Y| = n` for `SEARCH_n` and `2` otherwise.
**Correction:** (i) needs `n ≥ 2` (at `n = 1`, `SEARCH_1` has one answer and the one-element list
succeeds with probability `1` without queries); (ii) and (iii) need `n ≥ 1` (at `n = 0` the
`OR_0` distribution is undefined and no query algorithm exists). -/
theorem theorem_1_10 :
    ∃ c c'' : ℝ, 0 < c ∧ 0 < c'' ∧ ∀ (n k m : ℕ), 1 ≤ k → k ≤ m →
      (2 ≤ n → ∀ (b T : ℕ) (A : QueryAlg (Fin m × Fin n) (ZMod 2) (Fin b) T)
          (out : ((Fin m × Fin n) × ZMod 2) × Fin b → Finset (Fin m → Fin n)),
          (T : ℝ) ≤ c * k * Real.sqrt n →
          ∑ x ∈ prodDomain (searchDom n) m,
              prodDist (searchDist n) m x * successProb A out (listRel k m (searchRel n)) x ≤
            (2 : ℝ) ^ (-(c'' * k))) ∧
      (1 ≤ n → ∀ (b T : ℕ) (A : QueryAlg (Fin m × Fin n) (ZMod 2) (Fin b) T)
          (out : ((Fin m × Fin n) × ZMod 2) × Fin b → Finset (Fin m → ZMod 2)),
          (T : ℝ) ≤ c * k * Real.sqrt n →
          ∑ x ∈ prodDomain (Finset.univ : Finset (Fin n → ZMod 2)) m,
              prodDist (orDist n) m x *
                successProb A out (listRel k m (fun x y => orFn n x = y)) x ≤
            (2 : ℝ) ^ (-(c'' * k))) ∧
      (1 ≤ n → ∀ (b T : ℕ) (A : QueryAlg (Fin m × Fin n) (ZMod 2) (Fin b) T)
          (out : ((Fin m × Fin n) × ZMod 2) × Fin b → Finset (Fin m → ZMod 2)),
          (T : ℝ) ≤ c * k * n →
          ∑ x ∈ prodDomain (Finset.univ : Finset (Fin n → ZMod 2)) m,
              prodDist (parityDist n) m x *
                successProb A out (listRel k m (fun x y => parityFn n x = y)) x ≤
            (2 : ℝ) ^ (-(c'' * k))) := by sorry

end SelectiveDPT.Supplement
