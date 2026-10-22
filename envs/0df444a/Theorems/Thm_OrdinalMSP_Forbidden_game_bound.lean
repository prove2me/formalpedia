-- Prove2me | Theorems.Thm_OrdinalMSP_Forbidden_game_bound
-- name    : OrdinalMSP.Forbidden.game_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:55.194088+00:00
-- url     : https://prove2.me/theorems/354bdd67-4afe-4183-b7c0-9edf07bda0ce
-- title:
--   Proof of Lemma 1, pp. 9–10 — the right-hand side of (5) is at least ∫_p^1 (p/τ)^k dτ
-- statement:
--   Let $n \ge 1$ and $k \ge 1$ be integers and $0 < p \le 1$. Then
--   $$\int_p^1 \left(\frac{p}{\tau}\right)^k d\tau \ \le\ \sum_{s=0}^{n} \binom{n}{s} p^s (1-p)^{n-s}\, \frac1n \sum_{t=s+1}^{n} \prod_{j=s+1}^{t-1} \left(1 - \frac{k}{j}\right)_+ ,$$
--   with $x_+ = \max\{0, x\}$.
--
--   The right-hand side is the bound of display (5). The paper evaluates it through an auxiliary game: $n$ players arrive at independent uniform times in $[0,1]$, each player arriving after time $p$ picks $k$ partners among the earlier arrivals, and a player wins if she arrives after $p$ and all her partners arrive before $p$. The probability that a given player wins equals the right-hand side of (5), and conditioning on her arrival time $\tau$ shows that it is at least $\int_p^1 (p/\tau)^k\,d\tau$. The statement here is the resulting inequality between the two real expressions; it turns the combinatorial bound (5) into a closed form independent of $n$.
--
--   **Formalization Note** The auxiliary game is a proof device and is not formalized; the milestone is the composite "right-hand side of (5) $=$ Pr(a given player wins) $\ge \int_p^1 (p/\tau)^k d\tau$" stated as an inequality of real numbers. The integral is the interval integral over $[p, 1]$; $1 - k/j$ is computed in $\mathbb R$.
-- source:
--   Soto, Turkieltaub & Verdugo, Strong Algorithms for the Ordinal Matroid Secretary Problem, arXiv:1802.01997v1, proof of Lemma 1, pp. 9–10 ("the probability that a given person x wins is exactly the right hand side of (5)" and the display ∫_p^1 … ≥ ∫_p^1 (p/τ)^k dτ)

import Mathlib

namespace OrdinalMSP.Forbidden

theorem game_bound (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∫ τ in p..1, (p / τ) ^ k) ≤
      ∑ s ∈ Finset.range (n + 1),
        (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) *
          ((1 / (n : ℝ)) *
            ∑ t ∈ Finset.Icc (s + 1) n,
              ∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ))) := by sorry

end OrdinalMSP.Forbidden
