-- Prove2me | Theorems.Thm_QueryDepthMIS_lemma_3_5
-- name    : QueryDepthMIS.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:40:23.310189+00:00
-- url     : https://prove2.me/theorems/da2e1895-ec2d-4786-af08-64843afd62ba
-- title:
--   Lemma 3.5 — the protected sets are disjoint, ordered, and of equal size inside an interval
-- statement:
--   Fix $\alpha \in (0, 1/10)$. There is $A_0$ (depending on $\alpha$) such that for every $A \ge A_0$ the following holds. Let $\beta \in (0, 1)$, $n \ge 2$, $L = \lceil \sqrt{A}\,\log n \rceil$ ($\log$ to base 2), and let $P = (p_1, \dots, p_L)$ be positions with
--   $$
--   A \log n < p_1 < p_2 < \cdots < p_L < \beta n .
--   $$
--   With the intervals $I_i$, occupancies $s_i = |P \cap I_i|$, block lengths $\ell_i$ and protected sets $P_k$ of §3.4,
--   the sets $P, P_2, \dots, P_L$ are pairwise disjoint and satisfy
--
--   1. (P1) $P_2 < \cdots < P_L$;
--   2. (P2) $P_k < p_{k-1}$ for every $2 \le k \le L$;
--   3. (P3) if $p_k = p_{i,j}$ with $2 \le j < s_i$, then $|P_k| = |P_{k+1}| = \ell_i$.
--
--   Here $A < B$ means every element of $A$ is smaller than every element of $B$. These properties make the hop lemmas applicable to $(P_k, P_{k+1}, p_k, p_{k+1}, p_{k+2})$ along the exposure procedure.
--
--   Differences from the source:
--   - reading: for sufficiently large A depending on α → ∀ α, ∃ A₀, ∀ A ≥ A₀ (A₀ chosen after α, before β, n, P); reason: the quantifier order the phrase states
--   - reading: the standing setting of §3.4: β ∈ (0, 1) a small constant, n ≥ 2, L = ⌈√A · log n⌉, A log n < p₁ < ⋯ < p_L < βn → hypotheses: 0 < β < 1, 2 ≤ n, P a strictly increasing list of length ⌈√A · log₂ n⌉ with every entry in (A log₂ n, βn); reason: these are the paper's standing assumptions (pp.7, 11, 14) made explicit; the statement is deterministic and holds for every such β
--   - reading: (P1) P₂ < ⋯ < P_L → P_k < P_{k'} for all 2 ≤ k < k' ≤ L; reason: the chain notation; for nonempty sets the two agree, and the all-pairs form is what the proof gives (B₁ < ⋯ < B_L)
--   - encoding: p_k = p_{i,j} → i is the index of the interval containing p_k and j its rank within P ∩ I_i (the definitions ivIdx and jIdx); k is 1-based; reason: names for the paper's indices
--   - encoding: the standing assumption of §3.1 (p.11), 'we also assume, without loss of generality, that n ≥ n₀ for a sufficiently large constant n₀' → every n ≥ 2; reason: P is nonempty with A log₂ n < p₁ < βn < n, so n > A ≥ A₀; enlarging A₀ to at least n₀ makes the two versions equivalent
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.5, pp.14–15

import Mathlib
import Definitions.Def_QueryDepthMIS_prot
import Definitions.Def_QueryDepthMIS_sOcc

set_option autoImplicit false

namespace QueryDepthMIS

/-- Lemma 3.5 (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.5, pp.14–15): "Fix α ∈ (0, 1/10). For sufficiently large A
depending on α, the sets P, P₂, …, P_L are pairwise disjoint and satisfy: (P1) P₂ < ⋯ < P_L;
(P2) P_k < p_{k−1} for every 2 ≤ k ≤ L; (P3) if p_k = p_{i,j} with 2 ≤ j < s_i, then
|P_k| = |P_{k+1}| = ℓ_i."

**Formalization Note** The standing setting of §3.4 (pp.11, 14): `n ≥ 2`, `β ∈ (0, 1)`, `L = ⌈√A · log n⌉`, and a
position sequence `P = [p₁, …, p_L]` (a list of naturals, strictly increasing) with
`A log n < p₁ < ⋯ < p_L < βn`; `log` is `Real.logb 2`. "For sufficiently large A depending on α"
is read as `∃ A₀, ∀ A ≥ A₀` after `α` and before everything else. The protected set `P_k` is `prot α n P k`
(1-based `k`), `p_k = P[k − 1]`; "pairwise disjoint" is stated as `P_k ∩ P = ∅` and
`P_k ∩ P_{k'} = ∅` for `2 ≤ k < k' ≤ L`; `A < B` for sets means every element of `A` is below
every element of `B`, and (P1) is stated for all pairs `k < k'`; `p_{i,j}` is expressed through
the interval index `ivIdx` and the in-interval index `jIdx`. -/
theorem lemma_3_5 :
    ∀ α : ℝ, 0 < α → α < 1 / 10 → ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
    ∀ (β : ℝ), 0 < β → β < 1 →
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (P : List ℕ), P.length = ⌈Real.sqrt A * Real.logb 2 n⌉₊ → P.IsChain (· < ·) →
      (∀ p ∈ P, A * Real.logb 2 n < (p : ℝ) ∧ (p : ℝ) < β * n) →
      (∀ k, 2 ≤ k → k ≤ P.length → ∀ x ∈ prot α n P k, x ∉ P) ∧
      (∀ k k', 2 ≤ k → k < k' → k' ≤ P.length → Disjoint (prot α n P k) (prot α n P k')) ∧
      (∀ k k', 2 ≤ k → k < k' → k' ≤ P.length →
        ∀ x ∈ prot α n P k, ∀ y ∈ prot α n P k', x < y) ∧
      (∀ k, 2 ≤ k → k ≤ P.length → ∀ x ∈ prot α n P k, x < P.getD (k - 2) 0) ∧
      (∀ k, 1 ≤ k → k ≤ P.length →
        2 ≤ jIdx α n P (P.getD (k - 1) 0) →
        jIdx α n P (P.getD (k - 1) 0) < sOcc α n P (ivIdx α n (P.getD (k - 1) 0)) →
        (prot α n P k).card = ell α n P (ivIdx α n (P.getD (k - 1) 0)) ∧
        (prot α n P (k + 1)).card = ell α n P (ivIdx α n (P.getD (k - 1) 0))) := by sorry

end QueryDepthMIS
