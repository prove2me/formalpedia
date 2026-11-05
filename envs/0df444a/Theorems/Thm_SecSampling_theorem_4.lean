-- Prove2me | Theorems.Thm_SecSampling_theorem_4
-- name    : SecSampling.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:26.380004+00:00
-- url     : https://prove2.me/theorems/7fa723ae-f0be-4430-92ad-28138a3719e3
-- title:
--   Theorem 4 — no strategy for the colored last zero problem beats $kp^k(1-p)$
-- statement:
--   Let $p\in(0,1)$ and $k=\lfloor 1/(1-p)\rfloor$. For every (deterministic or randomized) strategy $Q$ for the colored last zero problem, every $\varepsilon>0$ and every $N_0$, there are integers $N_0\le m\le n$ such that the performance of $Q$ on $(m,n)$ is less than
--   $$k\,p^{k}(1-p)+\varepsilon .$$
--
--   Knowing the size $n$ and the numbers of red and blue ones therefore does not help asymptotically; with Proposition 6 this gives the negative half of Theorem 1 for players who know $n$.
--
--   Differences from the source:
--   - reading: no algorithm can achieve performance kpᵏ(1−p) + ε on every size n ≥ N₀ → for every N₀ there are N₀ ≤ m ≤ n with performance < kpᵏ(1−p) + ε; reason: in the colored problem "m basically plays the role that n was playing before" (p.26); requiring m ≥ N₀ as well as n ≥ N₀ is the stronger reading
--   - reading: the player wins if she stops on the last red 0 of the sequence (Definition 3) → an instance with no red 0 is won by every strategy; reason: the page leaves this case open; it is the convention of p.2, it only raises the performance (by pᵐ), so the bound is the harder one
--   - encoding: an algorithm for the colored last zero problem → a function Q n r b h ∈ [0, 1], the stopping probability given the size, the red ones, the blue ones and the prefix; reason: behavioural randomization is equivalent to any external randomness under perfect recall (Kuhn); the proof of Theorem 4 covers "both ... deterministic and ... randomized algorithms" (p.27)
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Theorem 4, p.26 (PDF p.27), proof p.27

import Mathlib
import Definitions.Def_SecSampling_ColoredLastZero

namespace SecSampling

/-- **Theorem 4** (arXiv:2011.07869v1, p.26). In the colored last zero problem, no algorithm can
achieve performance `kpᵏ(1−p) + ε` on every size `n ≥ N₀`: for every colored strategy `Q`, every
`ε > 0` and every `N₀`, there are `N₀ ≤ m ≤ n` with performance of `Q` on `(m, n)` below
`kpᵏ(1−p) + ε`, where `k = ⌊1/(1−p)⌋`.

**Formalization Note.** Both `m` and `n` are at least `N₀` ("m basically plays the role that n
was playing before", p.26); this is the stronger of the two readings. -/
theorem theorem_4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (Q : ColStrategy) (hQ : IsColStrategy Q)
    (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ m n : ℕ, N₀ ≤ m ∧ m ≤ n ∧ perfColored p Q m n < guarantee p + ε := by sorry

end SecSampling
