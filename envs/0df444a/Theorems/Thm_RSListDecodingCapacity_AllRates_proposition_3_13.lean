-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_proposition_3_13
-- name    : RSListDecodingCapacity.AllRates.proposition_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:32.617031+00:00
-- url     : https://prove2.me/theorems/0e247aa4-e529-4e97-b10a-8685c12bff0a
-- title:
--   Proposition 3.13 (Interpolation) — a nonzero $Q\in\mathcal Q$ annihilating every sufficiently agreeing $P$
-- statement:
--   Let $q$ be prime, $\varepsilon,\theta\in(0,1)$ satisfy (21), and let $n\ge k\ge2$ with $k/n\le(1-\theta)\varepsilon$; let $A=\lceil\varepsilon n\rceil$, let $\alpha_1,\dots,\alpha_n\in\mathbb F_q$ be distinct evaluation points, and let $\mathcal Q\subseteq\mathbb F_q[X,Y_0,\dots,Y_d]$ be the interpolation space (19). Then for every received word $y\in\mathbb F_q^n$ there is a nonzero $Q\in\mathcal Q$ such that every polynomial $P$ of degree at most $k-1$ agreeing with $y$ in at least $A$ positions satisfies
--   $$Q\big(X,P(X),P^{[1]}(X),\dots,P^{[d]}(X)\big)\equiv0 .$$
--
--   This turns list decoding into solving the polynomial differential equation (10), the task of Theorem 2.1.
--
--   Differences from the source:
--   - reading: B = ⌈mA/(k−1)⌉ of (12) in the definition of 𝒬, undefined at k = 1 → hypothesis 2 ≤ k; reason: 𝒬 is defined only for k ≥ 2; at k = 1 the source statement has no meaning
--   - generalization: q a sufficiently large prime (standing convention of §2, p.12) → every prime q; reason: the statement holds over every prime field and the source specializes it to large q; the argument uses no lower bound on q
--   - encoding: Q(X, P, P^[1], …, P^[d]) ≡ 0 → hasseJetEval d Q P = 0 in 𝔽_q[X]; reason: identically zero as a polynomial
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.24, Proposition 3.13 (proof pp.24–25)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSListDecodingCapacity_AllRates_Parameters
import Definitions.Def_RSListDecodingCapacity_AllRates_InterpolationSpace

open Polynomial

namespace RSListDecodingCapacity.AllRates

/-- **Proposition 3.13 (Interpolation)** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027
submission #565, p.24). Let `ε, θ ∈ (0, 1)` satisfy (21), let `n ≥ k ≥ 2` with `k/n ≤ (1 − θ)ε`,
`A = ⌈εn⌉`, distinct evaluation points `α₁, …, αₙ ∈ 𝔽_q`, and `𝒬` the interpolation space of (19).
For every received word `y ∈ 𝔽_qⁿ` there is a nonzero `Q ∈ 𝒬` such that every `P` of degree at
most `k − 1` agreeing with `y` in at least `A` positions satisfies
`Q(X, P(X), P^{[1]}(X), …, P^{[d]}(X)) ≡ 0`. -/
theorem proposition_3_13 (q : ℕ) (hq : q.Prime) (ε θ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (h21 : Cond21 ε θ) (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hrate : (k : ℝ) / n ≤ (1 - θ) * ε) (α : Fin n → ZMod q) (hα : Function.Injective α)
    (y : Fin n → ZMod q) :
    ∃ Q ∈ sourceQ (ZMod q) ε θ n k, Q ≠ 0 ∧
      ∀ P : (ZMod q)[X], P.degree ≤ ((k - 1 : ℕ) : WithBot ℕ) →
        paramA ε n ≤ agreement α y P → hasseJetEval (paramD ε θ) Q P = 0 := by sorry

end RSListDecodingCapacity.AllRates
