-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_lemma_3_3
-- name    : RSListDecodingCapacity.AllRates.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:35.84443+00:00
-- url     : https://prove2.me/theorems/21fad5da-7c28-4b02-8412-01fea9c53da0
-- title:
--   Lemma 3.3 — growth bounds for $\Lambda(z)$
-- statement:
--   1. For every $d\ge1$ and every real $z\ge0$,
--   $$\Lambda(z)\le\frac{\big(z+\binom d2\big)^{d-1}}{((d-1)!)^2}.$$
--   2. Let $\varepsilon,\theta\in(0,1)$ satisfy (21) and let $d\ge\lceil\varepsilon^{-3/\theta}\rceil$; put $m=d^3$, $W=\lfloor(1+\theta/2)dm/\log(ed)\rfloor$ and $\mathcal B=\{c:\omega(c)\le W,\ |c|\le\lceil(1+3\theta/4)m\rceil\}$. Then
--   $$\Lambda(W+m)\le|\mathcal B|\,d^{\,2/(2+\theta)+\theta(1-\theta)/18}.$$
--
--   The second bound says that enlarging the weight budget from $W$ to $W+m$ multiplies the count by only a small power of $d$; it is the key input to the local rank bound (Lemma 3.12).
--
--   Differences from the source:
--   - generalization: first clause for the §3 parameter d (d ≥ 2) → every d ≥ 1; reason: the d = 1 instance (Λ = 1, right side 1) is trivially included; every source instance is covered
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.17, Lemma 3.3 (proofs pp.19–21)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Parameters

namespace RSListDecodingCapacity.AllRates

/-- **Lemma 3.3** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, p.17), both
statements.
1. For every `z ≥ 0`, `Λ(z) ≤ (z + (d choose 2))^{d−1} / ((d − 1)!)²`.
2. If `d ≥ ⌈ε^{−3/θ}⌉` and (21) holds, then, with `m = d³` and `W` of (18) (and `𝓑` built from them),
   `Λ(W + m) ≤ |𝓑| d^{2/(2+θ) + θ(1−θ)/18}`. -/
theorem lemma_3_3 :
    (∀ d : ℕ, 1 ≤ d → ∀ z : ℝ, 0 ≤ z →
      (Lambda d z : ℝ) ≤ (z + (d.choose 2 : ℝ)) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) ∧
    (∀ ε θ : ℝ, 0 < ε → ε < 1 → 0 < θ → θ < 1 → ∀ d : ℕ, paramD ε θ ≤ d → Cond21 ε θ →
      (Lambda d ((paramW θ d (paramM d) + paramM d : ℕ) : ℝ) : ℝ) ≤
        ((scriptB θ d (paramM d) (paramW θ d (paramM d))).card : ℝ) *
          (d : ℝ) ^ (2 / (2 + θ) + θ * (1 - θ) / 18)) := by sorry

end RSListDecodingCapacity.AllRates
