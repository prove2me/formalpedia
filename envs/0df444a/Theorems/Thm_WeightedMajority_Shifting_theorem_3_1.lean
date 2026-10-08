-- Prove2me | Theorems.Thm_WeightedMajority_Shifting_theorem_3_1
-- name    : WeightedMajority.Shifting.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:24.589725+00:00
-- url     : https://prove2.me/theorems/7639bc09-4674-436d-8a47-be96cb0cdb62
-- title:
--   Theorem 3.1 — on any partition into consecutive segments, WML makes at most Σᵢ min(lᵢ, (log(n/(βγ)) + mᵢ log(1/β))/log(1/u)) mistakes
-- statement:
--   Let $0 < \beta < 1$ and $0 < \gamma < \tfrac12$, and put $u = \frac{1+\beta}{2} + (1-\beta)\gamma$. Let $\mathcal S$ be a finite sequence of $T$ trials with binary predictions of a pool of $n \ge 1$ algorithms and binary labels, and let $\mathcal S_1, \dots, \mathcal S_k$ be a partition of $\mathcal S$ into $k$ consecutive segments: there are indices $0 = b_0 \le b_1 \le \dots \le b_k = T$ and $\mathcal S_i$ consists of the trials $t$ with $b_{i-1} \le t < b_i$. Let $l_i = b_i - b_{i-1}$ be the number of trials of $\mathcal S_i$, and let $m_i$ be the minimum, over the members of the pool, of the number of mistakes made on $\mathcal S_i$; the best member may be a different one for each segment.
--
--   Run WML with parameters $\beta, \gamma$ on $\mathcal S$ from positive initial weights, each at least $\beta\gamma/n$ times the total initial weight. Then the number $m$ of mistakes of WML on $\mathcal S$ satisfies
--   $$m \le \sum_{i=1}^{k} \min\left( l_i,\ \frac{\log\big(n/(\beta\gamma)\big) + m_i \log(1/\beta)}{\log(1/u)} \right).$$
--
--   WML does not know the segments. The theorem says that it tracks a target that shifts from one pool member to another, paying for each segment a logarithmic cost in $n$ plus a constant multiple of the mistakes of that segment's best member.
--
--   **Formalization Note** The paper's "partitioning of $\mathcal S$ into $k$ subsequences" is read as a partition into consecutive segments, as in the paper's own description of the scenario (Section 1, p. 217: "the original sequence is partitioned into $s$ segments"); for interleaved subsequences the inequality fails. Segments may be empty (then $b_{i-1} = b_i$ and the segment contributes $0$); $k = 0$ forces $T = 0$. The boundaries are `b : Fin (k+1) → ℕ`, monotone, with `b 0 = 0` and `b (Fin.last k) = T`, and segment $i$ (`i : Fin k`) runs from `b i.castSucc` to `b i.succ`. The natural logarithm is used (the base cancels). As in Lemma 3.1, $\gamma > 0$ is assumed because the bound is $+\infty$ at $\gamma = 0$.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 224, Theorem 3.1

import Mathlib
import Definitions.Def_WeightedMajority_Shifting_WML

namespace WeightedMajority.Shifting

theorem theorem_3_1 {n T : ℕ} (hn : 0 < n) {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2)
    (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool)
    (hrun : IsWMLRun β γ x ρ w lam)
    (hfloor : ∀ i, β * γ / (n : ℝ) * totalWeight (w 0) ≤ w 0 i)
    (k : ℕ) (b : Fin (k + 1) → ℕ) (hb_mono : Monotone b) (hb0 : b 0 = 0)
    (hbk : b (Fin.last k) = T) :
    (masterMistakes ρ lam : ℝ) ≤
      ∑ i : Fin k, min ((b i.succ - b i.castSucc : ℕ) : ℝ)
        ((Real.log ((n : ℝ) / (β * γ)) +
            (bestMistakesOn x ρ (b i.castSucc) (b i.succ) : ℝ) * Real.log (1 / β)) /
          Real.log (1 / uFactor β γ)) := by sorry

end WeightedMajority.Shifting
