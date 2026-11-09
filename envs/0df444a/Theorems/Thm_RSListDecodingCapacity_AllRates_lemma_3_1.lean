-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_lemma_3_1
-- name    : RSListDecodingCapacity.AllRates.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:44.127213+00:00
-- url     : https://prove2.me/theorems/41bedeae-a1b1-45cb-a4d5-f52a9ca9f54b
-- title:
--   Lemma 3.1 — the local constraints force multiplicity $m$
-- statement:
--   Let $q$ be prime, $d,m\in\mathbb N$, $(\alpha,y)\in\mathbb F_q^2$, $P\in\mathbb F_q[X]$ and $Q\in\mathbb F_q[X,Y_0,\dots,Y_d]$. Suppose $P(\alpha)=y$ and $Q$ satisfies the local constraints (16) at $(\alpha,y)$. Then
--   $$Q\big(\alpha+T,\ P(\alpha+T),\ P^{[1]}(\alpha+T),\dots,P^{[d]}(\alpha+T)\big)\equiv0\pmod{T^m}.$$
--
--   Hence $Q(X,P,P^{[1]},\dots,P^{[d]})$ has a root of multiplicity at least $m$ at every agreement point of $P$; this is the multiplicity half of Proposition 3.13.
--
--   Differences from the source:
--   - generalization: d, m the parameters of §3 → arbitrary natural numbers d, m; reason: the constraints (16) are defined for any d, m and the statement uses no relation between them; the §3 values are an instance
--   - generalization: q a sufficiently large prime (standing convention of §2, p.12) → every prime q; reason: the statement holds over every prime field and the source specializes it to large q; the argument uses no lower bound on q
--   - encoding: the formal variable T and ≡ 0 mod T^m → the variable X of 𝔽_q[X] and divisibility by X^m; reason: renaming of the univariate variable
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.14, Lemma 3.1

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_LocalConstraints

open Polynomial

namespace RSListDecodingCapacity.AllRates

/-- **Lemma 3.1** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, p.14).
Suppose `P(α) = y` and `Q` satisfies the local constraints (16) at `(α, y)`. Then
`Q(α + T, P(α + T), P^{[1]}(α + T), …, P^{[d]}(α + T)) ≡ 0 mod T^m`.
The univariate variable `T` is Lean's `X`; `none` is the variable `X` of `Q` and `some j` is `Y_j`. -/
theorem lemma_3_1 (q : ℕ) (hq : q.Prime) (d m : ℕ) (α y : ZMod q) (P : (ZMod q)[X])
    (Q : MvPolynomial (Option (Fin (d + 1))) (ZMod q))
    (hP : P.eval α = y) (hQ : SatisfiesLocal d m α y Q) :
    (X : (ZMod q)[X]) ^ m ∣
      MvPolynomial.aeval (fun v : Option (Fin (d + 1)) =>
        Option.elim v (C α + X) fun j => (hasseDeriv (j : ℕ) P).comp (C α + X)) Q := by sorry

end RSListDecodingCapacity.AllRates
