-- Prove2me | Theorems.Thm_QNatProofs_fact_3_2
-- name    : QNatProofs.fact_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:33.130426+00:00
-- url     : https://prove2.me/theorems/4f5de6ca-aefa-454d-9037-d1bf1abf47e2
-- title:
--   Fact 3.2 — exponential PRF security from subexponential security (security statement)
-- statement:
--   Let $\mathcal G=\{G_{m,k}\}$ be classically subexponentially secure with exponent $a\in(0,1)$ (Definition 3.2). For $n,\lambda,R\in\mathbb N$ let
--   $$
--   F_{n,\lambda,k}(x):=G_{m,k}(0^{m-n}x)_{1,\dots,R},\qquad m=(n+R+\lambda)^{\lceil1/a\rceil+1},\qquad x\in\{0,1\}^n,\ k\in\mathcal K_m .
--   $$
--   Then for every classical oracle algorithm $B$ there is $N_0$ such that for all $n,\lambda,R$ with $n+\lambda\ge N_0$: if $B$ runs in time at most $2^\lambda$, it distinguishes $\mathcal F_{n,\lambda}$ from a uniformly random function $\{0,1\}^n\to\{0,1\}^R$ with advantage at most $2^{-\lambda}$.
--
--   This upgrades subexponential to exponential security, the form the PRAL reduction consumes.
--
--   Differences from the source:
--   - generalization: Definition 3.2: there is a ∈ (0,1) such that for all sufficiently large m every oracle algorithm B of time ≤ 2^{m^a} has advantage ≤ 2^{−m^a} → ∃ a ∈ (0,1), ∀ uniform oracle algorithm B, ∀ᶠ m, for every auxiliary input z with |z| ≤ m: time ≤ 2^{m^a} on 1^m z → advantage ≤ 2^{−m^a} (IsSecureWithExp); reason: the threshold may depend on B, so the hypothesis is implied by the printed one (where for each large m every algorithm, which may hard-wire z, is covered)
--   - generalization: 𝒢 has uniform keys sampled in poly(m) time and functions evaluated in poly(m) time → KeyedFam: any nonempty finite key sets with the uniform law; no efficiency clauses; reason: weaker hypothesis; no step of the proof samples keys or evaluates 𝒢 classically (the reductions only query the oracle; PRAL needs no efficient sampling, p.9)
--   - generalization: for any R ∈ ℕ … for sufficiently large n + λ; an algorithm on no input → one threshold N₀ for all R simultaneously; B runs on (1^n, 1^λ, 1^R, z) for every auxiliary z with |z| ≤ n + R + λ; reason: a stronger conclusion: more distinguishers and a threshold uniform in R; it specializes to the printed statement for fixed R and empty z
--   - reading: Key sampling and evaluation take time poly(n + R + λ), and hence poly(n) whenever R and λ are polynomially bounded in n → not stated; reason: the mission's keyed families carry no efficiency data (paper.md decision 12), so the sentence has no Lean counterpart; it is the composition of G's evaluation with zero padding and truncation and is used by no statement of the mission
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Fact 3.2, p.16; proof p.17

import Mathlib
import Definitions.Def_QNatProofs_KeyedFam

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms.Complexity

/-- **Fact 3.2 (Exponential PRF security from subexponential security)** (Li, Parham, *Natural
proofs for quantum state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…),
p.16): "suppose the function family `𝒢 = {G_{m,k} : {0,1}^m → {0,1}^m}_{m∈ℕ, k∈𝒦_m}` satisfies
Definition 3.2 with exponent `a`. Then for any `R ∈ ℕ`, consider the function family
`ℱ_{n,λ} = {F_{n,λ,k} : {0,1}ⁿ → {0,1}^R}` defined as `F_{n,λ,k}(x) := G_{m,k}(0^{m−n}x)_{1,…,R}`,
where `m = (n+R+λ)^{⌈1/a⌉+1}`, for each `x ∈ {0,1}ⁿ`, `k ∈ 𝒦_m`. Then any classical algorithm
running in time `2^λ` cannot distinguish between `ℱ_{n,λ}` and a random function with advantage
better than `2^{-λ}` for sufficiently large `n + λ`."

**Formalization Note** The distinguisher is a uniform oracle algorithm (`OracleAlg`) on input
`(1ⁿ, 1^λ, 1^R, z)` with any auxiliary string `z` of length at most `n + R + λ`; the threshold
`N₀` for "sufficiently large `n + λ`" depends only on the algorithm, not on `R` or `z`. -/
theorem fact_3_2 (G : KeyedFam) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hG : G.IsSecureWithExp a)
    (B : OracleAlg) : ∃ N₀ : ℕ, ∀ n lam R : ℕ, N₀ ≤ n + lam → ∀ z : List Bool,
      z.length ≤ n + R + lam →
      B.TimeBounded n R (encNat n ++ encNat lam ++ encNat R ++ z) ((2 : ℝ) ^ lam) →
      oracleAdv B (encNat n ++ encNat lam ++ encNat R ++ z)
          (fun k : G.K (prfLen a n R lam) => prfTape G (prfLen a n R lam) n R k) ≤
        (2 : ℝ) ^ (-(lam : ℝ)) := by sorry

end QNatProofs
