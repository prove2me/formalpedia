-- Prove2me | Theorems.Thm_QueryDepthMIS_claim_3_6
-- name    : QueryDepthMIS.claim_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:34:43.667194+00:00
-- url     : https://prove2.me/theorems/1a829307-80ad-48ca-b3b0-ff746a6a0e92
-- title:
--   Claim 3.6 — numerical approximations: $\ell_i > 10^3$, $\ell_i \approx |I_{i-1}|/s_i$, $|I_i|/|I_{i-1}| \le 1+2\alpha$, $\tau < \min I_{i-1}$
-- statement:
--   Fix $\alpha \in (0, 1/10)$. There is $A_0$ (depending on $\alpha$) such that for every $A \ge A_0$ the following holds. Let $\beta \in (0, 1)$, $n \ge 2$, $L = \lceil \sqrt{A}\,\log n \rceil$ ($\log$ to base 2), and let $P = (p_1, \dots, p_L)$ be positions with
--   $$
--   A \log n < p_1 < p_2 < \cdots < p_L < \beta n .
--   $$
--   With the intervals $I_i$, occupancies $s_i = |P \cap I_i|$, block lengths $\ell_i$ and protected sets $P_k$ of §3.4,
--   every occupied interval $I_i$ satisfies
--   $$
--   \ell_i > 10^3,\qquad (1 - \alpha)\frac{|I_{i-1}|}{s_i} \le \ell_i \le \frac{|I_{i-1}|}{s_i},\qquad \frac{|I_i|}{|I_{i-1}|} \le 1 + 2\alpha,\qquad \tau < \min I_{i-1},
--   $$
--   where $\tau = \lceil 18 \ln n \rceil$.
--
--   Differences from the source:
--   - reading: for sufficiently large A depending on α → ∀ α, ∃ A₀, ∀ A ≥ A₀ (A₀ chosen after α, before β, n, P); reason: the quantifier order the phrase states
--   - reading: the standing setting of §3.4: β ∈ (0, 1) a small constant, n ≥ 2, L = ⌈√A · log n⌉, A log n < p₁ < ⋯ < p_L < βn → hypotheses: 0 < β < 1, 2 ≤ n, P a strictly increasing list of length ⌈√A · log₂ n⌉ with every entry in (A log₂ n, βn); reason: these are the paper's standing assumptions (pp.7, 11, 14) made explicit; the statement is deterministic and holds for every such β
--   - encoding: τ < min I_{i−1} → τ < x for every x ∈ I_{i−1}; reason: I_{i−1} is nonempty because ℓ_i > 0, so the two agree
--   - encoding: the standing assumption of §3.1 (p.11), 'we also assume, without loss of generality, that n ≥ n₀ for a sufficiently large constant n₀' → every n ≥ 2; reason: P is nonempty with A log₂ n < p₁ < βn < n, so n > A ≥ A₀; enlarging A₀ to at least n₀ makes the two versions equivalent
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Claim 3.6, display (1), p.15

import Mathlib
import Definitions.Def_QueryDepthMIS_ell

set_option autoImplicit false

namespace QueryDepthMIS

/-- Claim 3.6 (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Claim 3.6, display (1), p.15): "For sufficiently large A depending on α,
every occupied interval I_i satisfies ℓ_i > 10³, (1 − α)|I_{i−1}|/s_i ≤ ℓ_i ≤ |I_{i−1}|/s_i,
|I_i|/|I_{i−1}| ≤ 1 + 2α, and τ < min I_{i−1}."

**Formalization Note** The standing setting of §3.4 (pp.11, 14): `n ≥ 2`, `β ∈ (0, 1)`, `L = ⌈√A · log n⌉`, and a
position sequence `P = [p₁, …, p_L]` (a list of naturals, strictly increasing) with
`A log n < p₁ < ⋯ < p_L < βn`; `log` is `Real.logb 2`. "For sufficiently large A depending on α"
is read as `∃ A₀, ∀ A ≥ A₀` after `α` and before everything else. `α ∈ (0, 1/10)` as in Lemma 3.5 (p.14);
`τ = ⌈18 ln n⌉` (p.14, `ln` = `Real.log`); "τ < min I_{i−1}" is stated as `τ < x` for every
`x ∈ I_{i−1}` (nonempty since `ℓ_i > 0`). -/
theorem claim_3_6 :
    ∀ α : ℝ, 0 < α → α < 1 / 10 → ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A →
    ∀ (β : ℝ), 0 < β → β < 1 →
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (P : List ℕ), P.length = ⌈Real.sqrt A * Real.logb 2 n⌉₊ → P.IsChain (· < ·) →
      (∀ p ∈ P, A * Real.logb 2 n < (p : ℝ) ∧ (p : ℝ) < β * n) →
    ∀ i : ℕ, 0 < sOcc α n P i →
      (10 : ℝ) ^ 3 < (ell α n P i : ℝ) ∧
      (1 - α) * ((Iv α n (i - 1)).card : ℝ) / (sOcc α n P i : ℝ) ≤ (ell α n P i : ℝ) ∧
      (ell α n P i : ℝ) ≤ ((Iv α n (i - 1)).card : ℝ) / (sOcc α n P i : ℝ) ∧
      ((Iv α n i).card : ℝ) / ((Iv α n (i - 1)).card : ℝ) ≤ 1 + 2 * α ∧
      ∀ x ∈ Iv α n (i - 1), ⌈18 * Real.log n⌉₊ < x := by sorry

end QueryDepthMIS
