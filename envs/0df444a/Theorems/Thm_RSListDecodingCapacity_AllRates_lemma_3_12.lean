-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_lemma_3_12
-- name    : RSListDecodingCapacity.AllRates.lemma_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:55.389774+00:00
-- url     : https://prove2.me/theorems/8c8e7f0b-35f7-4867-a681-faf570feede3
-- title:
--   Lemma 3.12 (Local rank) — $\operatorname{rank}\Gamma<|\mathcal B|m^3d^{-2\theta/(5+\theta)}$
-- statement:
--   Let $q$ be prime and $\varepsilon,\theta\in(0,1)$ satisfy (21). With $d=\lceil\varepsilon^{-3/\theta}\rceil$, $m=d^3$, $W$ of (18), $\mathcal B$ as in Section 3.1, and $\Gamma:V\to\mathbb F_q^I$ the map of Section 3.2.2,
--   $$\operatorname{rank}\Gamma<|\mathcal B|\,m^3\,d^{-\frac{2\theta}{5+\theta}}. \tag{25}$$
--
--   Each received point therefore imposes fewer than $|\mathcal B|m^3d^{-2\theta/(5+\theta)}$ independent local constraints, which is what Proposition 3.13 compares with $\dim\mathcal Q$.
--
--   Differences from the source:
--   - generalization: q a sufficiently large prime (standing convention of §2, p.12) → every prime q; reason: the statement holds over every prime field and the source specializes it to large q; the argument uses no lower bound on q
--   - encoding: rank Γ → Module.finrank of the range of Γ; reason: the rank of a linear map is the dimension of its image
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.23, Lemma 3.12, (25) (proof pp.23–24)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Parameters
import Definitions.Def_RSListDecodingCapacity_AllRates_LocalRank

namespace RSListDecodingCapacity.AllRates

/-- **Lemma 3.12 (Local rank)** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565,
p.23), (25): at the parameters of §3 — `ε, θ ∈ (0, 1)` with (21), `d = ⌈ε^{−3/θ}⌉`, `m = d³`, `W`
of (18) —
`rank Γ < |𝓑| m³ d^{−2θ/(5+θ)}`. -/
theorem lemma_3_12 (q : ℕ) (hq : q.Prime) (ε θ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (h21 : Cond21 ε θ) :
    (Module.finrank (ZMod q) (LinearMap.range (Gamma (ZMod q) (paramD ε θ)
        (paramM (paramD ε θ)) (paramW θ (paramD ε θ) (paramM (paramD ε θ))))) : ℝ) <
      ((scriptB θ (paramD ε θ) (paramM (paramD ε θ))
          (paramW θ (paramD ε θ) (paramM (paramD ε θ)))).card : ℝ) *
        (paramM (paramD ε θ) : ℝ) ^ 3 * (paramD ε θ : ℝ) ^ (-(2 * θ) / (5 + θ)) := by sorry

end RSListDecodingCapacity.AllRates
