-- Prove2me | Theorems.Thm_RandomQueryXOR_claim_4_7
-- name    : RandomQueryXOR.claim_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:11:41.401228+00:00
-- url     : https://prove2.me/theorems/30ba404c-6bd4-4d5b-9ee2-da9051d654e2
-- title:
--   Claim 4.7 — $\pi_L$ produces uniform indices; $h$ occurs more than $k$ times with probability $\le 1/n^2$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ and $x^\star$ have at least one sensitive zero, and let $k$ satisfy
--   $$
--   k\ \ge\ \frac{4T\log_2 n}{n}\qquad\text{and}\qquad k\ \ge\ 4\log_2 n .
--   $$
--   Then the index sequence $L=(\ell_1,\dots,\ell_T)$ produced by protocol $\pi_L$ is uniformly distributed on $[2n]^T$: every $L\in[2n]^T$ has probability $(2n)^{-T}$. Moreover, the probability that $h$ occurs more than $k$ times among $m_1,\dots,m_T$ is at most $1/n^2$.
--
--   The first part means the branching program sees exactly its intended input distribution although the sides $\rho$ of the two-bit game are planted into $L$; the second bounds the probability that $\pi_{\rm two}$ runs out of players.
--
--   Differences from the source:
--   - generalization: k ≥ (4T log n)/n, with T the length of the §4.2 program P solving g_{f⊕} with success 2/3 → k ≥ 4T log₂ n / n and k ≥ 4 log₂ n, for every T; reason: the standing assumption of §4.2 gives a program P of length T computing g_{f⊕} with success 2/3 in the gate-keeper model; P must see index 2h with b = 1 with probability ≥ 1/3 (it distinguishes y from y ⊕ e_{2h}), so T/(4n) ≥ 1/3, T ≥ n and k ≥ 4T log₂ n / n ≥ 4 log₂ n: the Lean hypothesis is implied by the source hypotheses, so the statement specializes to it. The printed k ≥ (4T log n)/n alone does not suffice (n = 256, T = 3, k = 1: Pr[Bin(3, 1/256) ≥ 2] = 3/n² − 2/n³ > 1/n²), but that instance violates the standing assumption
--   - encoding: h uniform on the sensitive zeros of x⋆_f → a hypothesis that x⋆ has a sensitive zero, so that h exists; reason: a nondegeneracy condition: π_L is undefined without it
--   - generalization: x⋆_f a maximum-sensitivity input with sens0 ≥ sens1 (Assumption 4.2) → any x⋆ with at least one sensitive zero; reason: the proof uses only that h ranges over the nonempty set of sensitive zeros of x⋆
--   - encoding: log → Real.logb 2 (base 2); reason: the paper measures memory in bits; Real.logb 2 0 = 0 makes T = 0 harmless
--   - encoding: a uniformly random sequence of T integers → every L ∈ (Fin (2 * n))^T has probability (2n)^{-T} under the law of (h, M, coins, ρ); reason: the definition of uniformity on [2n]^T
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Claim 4.7, p.19 (PDF p.21); standing hypothesis k ≥ (4T log n)/n on the same page

import Mathlib
import Definitions.Def_RandomQueryXOR_cmi
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_RandomQueryXOR_piL

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT

/-- Claim 4.7 (Garg, Sundaresan, Velusamy, *XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.19 = PDF p.21): "Protocol π_L generates a uniformly random
sequence of T integers. Moreover, the probability that this sequence contains more than k values m_t
for t ∈ [T] with m_t = h is at most 1/n²", under the standing "We work with k ≥ (4T log n)/n" and, in place of
the standing assumption of §4.2 that `T` is the length of a program solving `g_{f⊕}`, the weaker
hypothesis `k ≥ 4 log₂ n`.

**Formalization Note** The second sentence needs more than `k ≥ (4T log n)/n`: `n = 256`, `T = 3`,
`k = 1` gives `Pr[≥ 2 occurrences] = 3/n² − 2/n³ > 1/n²`. In the paper `T` is the length of the
program `P` of §4.2, which computes `g_{f⊕}` with success `2/3` in the gate-keeper model; such a
program must see index `2h` with `b = 1` with probability at least `1/3` (it distinguishes `y` from
`y ⊕ e_{2h}`), so `T/(4n) ≥ 1/3`, `T ≥ n`, and `k ≥ 4T log₂ n / n ≥ 4 log₂ n`. The hypothesis
`k ≥ 4 log₂ n` replaces that standing assumption (it is implied by it). `log` is base 2. Uniformity means: every `L ∈ [2n]^T` has probability
`(2n)^{−T}` under the law of π_L's randomness (`h` uniform on the sensitive zeros of `x⋆ = xs`, which
must exist). -/
theorem claim_4_7 {n T : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (k : ℕ)
    (hZ : (sensZeros f xs).Nonempty)
    (hk : 4 * (T : ℝ) * Real.logb 2 n / n ≤ k) (hk' : 4 * Real.logb 2 n ≤ k) :
    (∀ L : Fin T → Fin (2 * n),
      probOf (piLLaw (T := T) f xs k hZ) (fun ω => piL k ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = L) =
        ((2 * n : ℝ) ^ T)⁻¹) ∧
    probOf (piLLaw (T := T) f xs k hZ) (fun ω => k < occCount ω.1 ω.2.1) ≤ 1 / (n : ℝ) ^ 2 := by sorry

end RandomQueryXOR
