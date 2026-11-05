-- Prove2me | Theorems.Thm_SecSampling_proposition_4
-- name    : SecSampling.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:13.821336+00:00
-- url     : https://prove2.me/theorems/d20822ab-b6c6-48f9-b256-fc51125d0235
-- title:
--   Proposition 4 — in the last zero problem no strategy beats the $k$-max guarantee, from any $N_0$
-- statement:
--   Let $p\in(0,1)$ and $k=\lfloor 1/(1-p)\rfloor$. For every (deterministic or randomized) strategy $q$ for the last zero problem, every $\varepsilon>0$ and every $N_0$, there is a size $n\ge N_0$ at which the performance of $q$ is less than
--   $$k\,p^{k}(1-p)+\varepsilon .$$
--
--   The $k$-max strategy has performance $kp^k(1-p)+p^n$ at every size $n\ge k+1$, so its guarantee from any $N_0$ is $kp^k(1-p)$; the proposition says no strategy that does not know $n$ has a larger one.
--
--   Differences from the source:
--   - encoding: no algorithm can achieve a better success guarantee than the k-max algorithm, starting from an arbitrary N₀ → for every ε > 0 and N₀ some size n ≥ N₀ has performance < kpᵏ(1−p) + ε; reason: the guarantee from N₀ is an infimum over n ≥ N₀, and k-max's equals kpᵏ(1−p) (Lemma 1 (ii) through the increasing reduction); the ε-form says exactly that no strategy's infimum exceeds it
--   - reading: the player wins if she stops on the last 0 of the sequence (Definition 1) → a string with no 0 is won by every strategy; reason: the page leaves this case open; p.2 declares it a win by vacuity for AOSp, and it changes the performance at size n by pⁿ only
--   - encoding: a randomized algorithm for the last zero problem → a function q m h ∈ [0, 1], the stopping probability given the norm m and the prefix h seen so far; reason: behavioural randomization is equivalent to any external randomness under perfect recall (Kuhn); it is one probability per information state of Definition 1
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Proposition 4, p.10 (PDF p.11); restated in §5.4

import Mathlib
import Definitions.Def_SecSampling_LastZero

namespace SecSampling

/-- **Proposition 4** (arXiv:2011.07869v1, p.10). For the last zero problem with any value of
`p`, no algorithm (deterministic or randomized) can achieve a better success guarantee than the
k-max algorithm, starting from an arbitrary `N₀`: for every strategy `q` (which does not know the
size), every `ε > 0` and every `N₀`, there is a size `n ≥ N₀` at which the performance of `q` is
below `kpᵏ(1−p) + ε`, with `k = ⌊1/(1−p)⌋`.

**Formalization Note.** `kpᵏ(1−p)` is the k-max guarantee from any `N₀` on: by Lemma 1 (ii)
through the increasing reduction, k-max's performance at size `n ≥ k + 1` is `kpᵏ(1−p) + pⁿ`. -/
theorem proposition_4 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (q : LZStrategy)
    (hq : IsLZStrategy q) (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ n : ℕ, N₀ ≤ n ∧ perfLZ p q n < guarantee p + ε := by sorry

end SecSampling
