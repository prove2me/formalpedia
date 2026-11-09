-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_lemma_3_10
-- name    : RSListDecodingCapacity.AllRates.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:38.95235+00:00
-- url     : https://prove2.me/theorems/04186e97-0e09-46e2-a700-28440f726eb2
-- title:
--   Lemma 3.10 — divisibility by $T^rE^h$ with $r+dh\ge m$ puts $F$ in $\ker\Gamma$
-- statement:
--   Let $d\ge1$, $m$, $W$ be natural numbers and $V$, $\Gamma:V\to\mathbb F_q^I$, $E$ as in Section 3.2.2. Suppose $F\in V$ is divisible by $T^rE^h$ for some $r,h\ge0$ with $r+dh\ge m$, divisibility taken in $\mathbb F_q[T,U,Y_1,\dots,Y_d]/(T^m)$, where $V$ lives: $F\equiv T^rE^hG\pmod{T^m}$ for some polynomial $G$. Then
--   $$F\in\ker\Gamma .$$
--
--   This is the membership criterion used to exhibit a large subspace of $\ker\Gamma$ in Lemma 3.11.
--
--   Differences from the source:
--   - generalization: d, m, W the parameters of §3 (d = ⌈ε^(−3/θ)⌉, m = d³, W of (18)) → arbitrary natural numbers d ≥ 1, m, W; reason: V, I and Γ are defined from d, m, W alone and the statement uses no relation between them; the §3 values are an instance
--   - generalization: q a sufficiently large prime (standing convention of §2, p.12) → every prime q; reason: the statement holds over every prime field and the source specializes it to large q; the argument uses no lower bound on q
--   - encoding: F divisible by T^r E^h in F_q[T,U,Y]/(T^m) → ∃ G, F − T^r E^h G ∈ (T^m); reason: this is divisibility in the quotient ring; V is represented by monomials of T-degree below m
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.22, Lemma 3.10

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_LocalRank

open MvPolynomial

namespace RSListDecodingCapacity.AllRates

/-- **Lemma 3.10** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, p.22).
Suppose `F ∈ V` is divisible by `T^r E^h` (in `𝔽[T, U, Y₁, …, Y_d]/(T^m)`, where `V` lives) for some
`r, h ≥ 0` with `r + d h ≥ m`. Then `F ∈ ker Γ`. -/
theorem lemma_3_10 (q : ℕ) (hq : q.Prime) (d m W : ℕ) (hd : 1 ≤ d)
    (F : Vspace (ZMod q) d m W) (r h : ℕ) (hrh : m ≤ r + d * h)
    (hdiv : ∃ G : MvPolynomial (UVar d) (ZMod q),
      F.1 - X UVar.T ^ r * Eelt (ZMod q) d ^ h * G ∈
        Ideal.span {(X UVar.T : MvPolynomial (UVar d) (ZMod q)) ^ m}) :
    F ∈ LinearMap.ker (Gamma (ZMod q) d m W) := by sorry

end RSListDecodingCapacity.AllRates
