-- Prove2me | Theorems.Thm_QueryDepthMIS_claim_3_8
-- name    : QueryDepthMIS.claim_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:40:17.942196+00:00
-- url     : https://prove2.me/theorems/b6e670c6-cdc4-4740-ba90-712e2cc0b505
-- title:
--   Claim 3.8 — $\prod_{k=2}^{L-1} 1/(e|P_k|) \le (en)^2(1-\alpha)^{-L}\prod_{i:s_i>0}(s_i/(e|I_{i-1}|))^{s_i}$
-- statement:
--   Fix $\alpha \in (0, 1/10)$. There is $A_0$ (depending on $\alpha$) such that for every $A \ge A_0$ the following holds. Let $\beta \in (0, 1)$, $n \ge 2$, $L = \lceil \sqrt{A}\,\log n \rceil$ ($\log$ to base 2), and let $P = (p_1, \dots, p_L)$ be positions with
--   $$
--   A \log n < p_1 < p_2 < \cdots < p_L < \beta n .
--   $$
--   With the intervals $I_i$, occupancies $s_i = |P \cap I_i|$, block lengths $\ell_i$ and protected sets $P_k$ of §3.4,
--   $$
--   \prod_{k=2}^{L-1} \frac{1}{e|P_k|} \le (en)^2 (1 - \alpha)^{-L} \prod_{i : s_i > 0} \left(\frac{s_i}{e|I_{i-1}|}\right)^{s_i},
--   $$
--   the product on the right running over the occupied intervals.
--
--   This rewrites the bound of Claim 3.7 in terms of the occupancy vector $(s_i)$, which is what the union bound over position sequences counts.
--
--   Differences from the source:
--   - reading: for sufficiently large A depending on α → ∀ α, ∃ A₀, ∀ A ≥ A₀ (A₀ chosen after α, before β, n, P); reason: the quantifier order the phrase states
--   - reading: the standing setting of §3.4: β ∈ (0, 1) a small constant, n ≥ 2, L = ⌈√A · log n⌉, A log n < p₁ < ⋯ < p_L < βn → hypotheses: 0 < β < 1, 2 ≤ n, P a strictly increasing list of length ⌈√A · log₂ n⌉ with every entry in (A log₂ n, βn); reason: these are the paper's standing assumptions (pp.7, 11, 14) made explicit; the statement is deterministic and holds for every such β
--   - encoding: the standing assumption of §3.1 (p.11), 'we also assume, without loss of generality, that n ≥ n₀ for a sufficiently large constant n₀' → every n ≥ 2; reason: P is nonempty with A log₂ n < p₁ < βn < n, so n > A ≥ A₀; enlarging A₀ to at least n₀ makes the two versions equivalent
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Claim 3.8, display (4), p.16

import Mathlib
import Definitions.Def_QueryDepthMIS_prot
import Definitions.Def_QueryDepthMIS_bNum

set_option autoImplicit false

namespace QueryDepthMIS

/-- Claim 3.8 (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Claim 3.8, display (4), p.16):
"∏_{k=2}^{L−1} 1/(e|P_k|) ≤ (en)²(1 − α)^{−L} ∏_{i:s_i>0} (s_i/(e|I_{i−1}|))^{s_i}."

**Formalization Note** The standing setting of §3.4 (pp.11, 14): `n ≥ 2`, `β ∈ (0, 1)`, `L = ⌈√A · log n⌉`, and a
position sequence `P = [p₁, …, p_L]` (a list of naturals, strictly increasing) with
`A log n < p₁ < ⋯ < p_L < βn`; `log` is `Real.logb 2`. "For sufficiently large A depending on α"
is read as `∃ A₀, ∀ A ≥ A₀` after `α` and before everything else. `α ∈ (0, 1/10)` as in Claim 3.6, on which the claim
rests; the product on the right runs over the occupied intervals `I_i`, `1 ≤ i ≤ b`;
`(1 − α)^{−L}` is `((1 − α)^L)⁻¹`. -/
theorem claim_3_8 :
    ∀ α : ℝ, 0 < α → α < 1 / 10 → ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
    ∀ (β : ℝ), 0 < β → β < 1 →
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (P : List ℕ), P.length = ⌈Real.sqrt A * Real.logb 2 n⌉₊ → P.IsChain (· < ·) →
      (∀ p ∈ P, A * Real.logb 2 n < (p : ℝ) ∧ (p : ℝ) < β * n) →
      ∏ k ∈ Finset.Icc 2 (P.length - 1), 1 / (Real.exp 1 * ((prot α n P k).card : ℝ)) ≤
        (Real.exp 1 * n) ^ 2 * ((1 - α) ^ P.length)⁻¹ *
          ∏ i ∈ (Finset.Icc 1 (bNum α n)).filter (fun i => 0 < sOcc α n P i),
            ((sOcc α n P i : ℝ) / (Real.exp 1 * ((Iv α n (i - 1)).card : ℝ))) ^ sOcc α n P i := by sorry

end QueryDepthMIS
