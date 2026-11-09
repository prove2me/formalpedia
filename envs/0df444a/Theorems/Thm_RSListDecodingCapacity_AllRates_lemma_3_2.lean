-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_lemma_3_2
-- name    : RSListDecodingCapacity.AllRates.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:34.895172+00:00
-- url     : https://prove2.me/theorems/e0e5af8f-75b7-47ad-a302-a5284be32297
-- title:
--   Lemma 3.2 — degree bounds and dimension of the interpolation space
-- statement:
--   Let $q$ be prime, $\varepsilon,\theta\in(0,1)$, and $n\ge k\ge2$ with the rate assumption (13) $k/n\le(1-\theta)\varepsilon$. Let $d,A,m,B,W,\mathcal B$ be the parameters of Section 3 and $\mathcal Q\subseteq\mathbb F_q[X,Y_0,\dots,Y_d]$ the interpolation space (19). Then:
--   1. every $Q\in\mathcal Q$ satisfies $\deg_{Y_i}Q\le B$ for each $i\in\{0,\dots,d\}$;
--   2. for every $Q\in\mathcal Q$ and every $P\in\mathbb F_q[X]$ with $\deg P\le k-1$,
--   $$\deg_X Q\big(X,P(X),P^{[1]}(X),\dots,P^{[d]}(X)\big)<mA;$$
--   3. $$\dim\mathcal Q>\frac{\theta^3}{384}\,|\mathcal B|\,(k-1)\,m^3 .$$
--
--   The degree bounds make the root-finding step of Theorem 2.1 applicable and force the substituted polynomial to vanish once it has $mA$ roots; the dimension bound is compared with the number of constraints in Proposition 3.13.
--
--   Differences from the source:
--   - reading: B = ⌈mA/(k−1)⌉ of (12), undefined at k = 1 → hypothesis 2 ≤ k; reason: the source's B (used by item 1 and by the space 𝒬) is defined only for k ≥ 2; the k = 1 case has no source meaning
--   - generalization: q a sufficiently large prime (standing convention of §2, p.12) → every prime q; reason: the statement holds over every prime field and the source specializes it to large q; the argument uses no lower bound on q
--   - encoding: deg_X of the substituted polynomial → Polynomial.degree in WithBot ℕ; reason: the zero polynomial has degree −∞, which is below mA; this is the source's convention for the zero polynomial
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), pp.15–16, Lemma 3.2

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSListDecodingCapacity_AllRates_Parameters
import Definitions.Def_RSListDecodingCapacity_AllRates_InterpolationSpace

open Polynomial

namespace RSListDecodingCapacity.AllRates

/-- **Lemma 3.2** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, pp.15–16), all
three items, at the parameters of §3: `ε, θ ∈ (0, 1)`, `n ≥ k`, the rate assumption (13)
`k/n ≤ (1 − θ)ε`, and `d, A, m, B, W, 𝓑` of (11), (12), (18). `k ≥ 2` makes `B = ⌈mA/(k−1)⌉`
defined.
1. every `Q ∈ 𝒬` has `deg_{Y_i} Q ≤ B` for `i = 0, …, d`;
2. for every `Q ∈ 𝒬` and `P` with `deg P ≤ k − 1`, `deg_X Q(X, P, P^{[1]}, …, P^{[d]}) < mA`;
3. `dim 𝒬 > (θ³/384) |𝓑| (k − 1) m³`. -/
theorem lemma_3_2 (q : ℕ) (hq : q.Prime) (ε θ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hrate : (k : ℝ) / n ≤ (1 - θ) * ε) :
    (∀ Q ∈ sourceQ (ZMod q) ε θ n k, ∀ j : Fin (paramD ε θ + 1),
        Q.degreeOf (some j) ≤ paramB (paramM (paramD ε θ)) (paramA ε n) k) ∧
    (∀ Q ∈ sourceQ (ZMod q) ε θ n k, ∀ P : (ZMod q)[X],
        P.degree ≤ ((k - 1 : ℕ) : WithBot ℕ) →
        (hasseJetEval (paramD ε θ) Q P).degree <
          ((paramM (paramD ε θ) * paramA ε n : ℕ) : WithBot ℕ)) ∧
    θ ^ 3 / 384 *
        ((scriptB θ (paramD ε θ) (paramM (paramD ε θ))
          (paramW θ (paramD ε θ) (paramM (paramD ε θ)))).card : ℝ) *
        ((k : ℝ) - 1) * (paramM (paramD ε θ) : ℝ) ^ 3 <
      (Module.finrank (ZMod q) (sourceQ (ZMod q) ε θ n k) : ℝ) := by sorry

end RSListDecodingCapacity.AllRates
