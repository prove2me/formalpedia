-- Prove2me | Theorems.Thm_SetCoverThreshold_SetCover_lemma_3_2
-- name    : SetCoverThreshold.SetCover.lemma_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:57:26.102506+00:00
-- url     : https://prove2.me/theorems/bd4f57a3-dad4-4b1e-8473-8f8b0f630077
-- title:
--   Lemma 3.2 — existence of partition systems with $d=(1-2/k)\,k\ln m$
-- statement:
--   For every $c\ge 0$ there is $m_0$ such that for all $m\ge m_0$ and all $L$, $k$ with
--
--   1. $L\le(\log_2 m)^c$,
--   2. $2\le k<\dfrac{\ln m}{3\ln\ln m}$,
--
--   there is a partition system $B(m,L,k,d)$ with
--
--   $$d=\left\lceil\Big(1-\frac{2}{k}\Big)\,k\ln m\right\rceil .$$
--
--   This is the existence part of Lemma 3.2 with the lemma's own choice $f(k)=2/k$. It shows that partition systems with $d$ close to $k\ln m$ exist for polylogarithmically many partitions, which is what makes the gap of the reduction approach $\ln N$.
--
--   **Formalization Note** "L ≃ (log m)^c" is read as $L\le(\log_2 m)^c$ (the paper's log is base 2, p. 635); a system for the largest such $L$ yields one for every smaller $L$ by dropping partitions. The threshold $m_0$ depends on $c$ only, not on $L$ or $k$. $d$ is rounded up, the strongest integer reading. The lemma's last sentence (a construction in ZTIME$(m^{O(\log m)})$) is not formalized: randomized time classes are not defined here.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), p. 644, Lemma 3.2 (existence part; f(k) = 2/k from its last sentence)

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem

namespace SetCoverThreshold.SetCover

theorem lemma_3_2 (c : ℝ) (hc : 0 ≤ c) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ L k : ℕ,
      (L : ℝ) ≤ (Real.logb 2 m) ^ c → 2 ≤ k →
        (k : ℝ) < Real.log m / (3 * Real.log (Real.log m)) →
          Nonempty (PartitionSystem m L k ⌈(1 - 2 / (k : ℝ)) * k * Real.log m⌉₊) := by sorry

end SetCoverThreshold.SetCover
