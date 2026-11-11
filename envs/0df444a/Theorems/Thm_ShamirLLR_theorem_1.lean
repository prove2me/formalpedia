-- Prove2me | Theorems.Thm_ShamirLLR_theorem_1
-- name    : ShamirLLR.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:14.969126+00:00
-- url     : https://prove2.me/theorems/4cf02af4-1529-4e5b-8fec-455e37ae3530
-- title:
--   Theorem 1 — relative degrees above one third: $\mathbb E_a\,\mathrm{Insec}(a;\lfloor cm\rfloor)\le 2(2/\pi)^{(1-\varepsilon)d}$
-- statement:
--   Let $\tau=2/\pi$ and let $\mathbb E_a$ denote the uniform average over $\mathcal A_{p,m}$, the ordered $m$-tuples of distinct nonzero places.
--
--   1. Fix $1/3<c<1/2$ and $0<\varepsilon<1$. There are constants $C_{c,\varepsilon},m_{c,\varepsilon}>0$ such that for $m\ge m_{c,\varepsilon}$, $d=\lfloor cm\rfloor$, and every odd prime $p$ with $\log p\ge C_{c,\varepsilon}\,m^2\log(2m)$,
--   $$
--   \mathbb E_a\,\Delta(a;d)\le\tau^{(1-\varepsilon)d},\qquad \mathbb E_a\,\mathrm{Insec}(a;d)\le2\,\tau^{(1-\varepsilon)d}. \tag{3}
--   $$
--   2. For every fixed $0<u<1/2$, if $m=\lfloor n^u\rfloor$ and $2^{n-1}<p<2^n$, then uniformly over these primes
--   $$
--   \mathbb E_a\,\Delta(a;d)\le\tau^{(1-o(1))d},\qquad \mathbb E_a\,\mathrm{Insec}(a;d)\le\tau^{(1-o(1))d}, \tag{4}
--   $$
--   where $o(1)\to0$ as $n\to\infty$ for fixed $c,u$.
--   3. More generally, the same asymptotic conclusion holds when $m\to\infty$ and $\log p/(m^2\log(2m))\to\infty$.
--
--   Since the LSB attack gives $\mathrm{Insec}(a;d)\ge\tau^d$, the base $2/\pi$ is optimal; the theorem gives local one-bit leakage resilience of multiplication-friendly Shamir sharing for almost all evaluation tuples.
--
--   Differences from the source:
--   - reading: (4) "uniformly over these primes … where $o(1)\to0$ as $n\to\infty$ for fixed $c, u$" → a function $o:\mathbb N\to\mathbb R$ with $o(n)\to0$, chosen after $c, u$ and before $n$ and $p$, with both bounds for all large $n$ and every prime $2^{n-1}<p<2^n$; reason: the printed quantifier order
--   - reading: "the same asymptotic conclusion holds when $m\to\infty$ and $\log p/(m^2\log(2m))\to\infty$" → for every $1/3<c<1/2$ and every sequence $(m_j,p_j)$ of naturals with $p_j$ prime, $m_j\to\infty$ and $\log p_j/(m_j^2\log(2m_j))\to\infty$, some $o_j\to0$ with both bounds for all large $j$; reason: the asymptotic statement along every admissible sequence
--   - encoding: "odd prime" in (3); "$2^{n-1}<p<2^n$" in (4) → `[Fact p.Prime]` with `p ≠ 2` in (3); prime $p$ in (4) and in the general clause; reason: in (4) and the general clause $p$ is eventually odd
--   - encoding: $\mathbb E_a$ over uniform ordered distinct nonzero tuples → the Finset average `avgTuples p m` over $\mathcal A_{p,m}$; reason: it is $0$ only on an empty $\mathcal A_{p,m}$, which the hypotheses exclude for large $m$ and $n$
--   - encoding: $d=\lfloor cm\rfloor$, $m=\lfloor n^u\rfloor$, $(2/\pi)^{(1-\varepsilon)d}$, $\log$ → natural floors, real powers, natural logarithm; reason: Lean conventions; $\log$ is natural (p.14)
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Theorem 1, Eq. (3)–(4), p.3 (PDF p.4); bit length $n$, p.2

import Mathlib
import Definitions.Def_ShamirLLR_evalTuples
import Definitions.Def_ShamirLLR_deltaClass
import Definitions.Def_ShamirLLR_insec

set_option autoImplicit false

open Filter Topology

namespace ShamirLLR

/-- **Theorem 1 (Relative degrees above one third).**
1. Fix `1/3 < c < 1/2` and `0 < ε < 1`. There are constants `C_{c,ε}, m_{c,ε} > 0` such that for
   `m ≥ m_{c,ε}`, `d = ⌊cm⌋`, and every odd prime `p` with `log p ≥ C_{c,ε} m² log(2m)`,
   `𝔼_a Δ(a; d) ≤ (2/π)^{(1−ε)d}` and `𝔼_a Insec(a; d) ≤ 2 (2/π)^{(1−ε)d}` (3).
2. For every fixed `0 < u < 1/2`, if `m = ⌊n^u⌋` and `2^{n−1} < p < 2^n`, then uniformly over
   these primes `𝔼_a Δ(a; d) ≤ (2/π)^{(1−o(1))d}` and `𝔼_a Insec(a; d) ≤ (2/π)^{(1−o(1))d}` (4),
   where `o(1) → 0` as `n → ∞` for fixed `c, u`.
3. More generally, the same asymptotic conclusion holds when `m → ∞` and
   `log p / (m² log(2m)) → ∞`.

Here `𝔼_a` is the uniform average over `A_{p,m}` (ordered tuples of distinct nonzero places).

Source: Hwang–Maji–Shkredov–Ye, *Local Leakage Resilience of Multiplication-friendly Shamir
Secret Sharing*, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…), Theorem 1,
Eq. (3)–(4), p.3; `n` the bit length of `p`, p.2.

**Formalization Note.** "Odd prime" is `[Fact p.Prime]` with `p ≠ 2` in (3); in (4) and in the
general clause `p` is prime as printed (it is eventually odd). `d = ⌊cm⌋` and `m = ⌊n^u⌋` are
natural floors; exponents are real powers; `log` is natural. The `o(1)` of (4) is a function
`o : ℕ → ℝ` tending to `0`, chosen after `c, u` and before `n` and the primes, and the bounds hold
for all large `n` and all primes in `(2^{n−1}, 2^n)`; in the general clause every sequence
`(m_j, p_j)` with the stated growth gets its own `o_j → 0`, and the bounds hold for all large `j`.
Averages over `A_{p,m}` are `0` when `A_{p,m} = ∅`, which the hypotheses exclude for large `m` and
`n`. -/
theorem theorem_1 :
    (∀ c ε : ℝ, 1 / 3 < c → c < 1 / 2 → 0 < ε → ε < 1 →
      ∃ C m₀ : ℝ, 0 < C ∧ 0 < m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
        C * (m : ℝ) ^ 2 * Real.log (2 * m) ≤ Real.log p →
          avgTuples p m (fun a => delta a ⌊c * m⌋₊) ≤
              (2 / Real.pi) ^ ((1 - ε) * (⌊c * m⌋₊ : ℝ)) ∧
            avgTuples p m (fun a => insec a ⌊c * m⌋₊) ≤
              2 * (2 / Real.pi) ^ ((1 - ε) * (⌊c * m⌋₊ : ℝ))) ∧
    (∀ c u : ℝ, 1 / 3 < c → c < 1 / 2 → 0 < u → u < 1 / 2 →
      ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
        ∀ (p : ℕ) [Fact p.Prime], 2 ^ (n - 1) < p → p < 2 ^ n →
          avgTuples p ⌊(n : ℝ) ^ u⌋₊ (fun a => delta a ⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊) ≤
              (2 / Real.pi) ^ ((1 - o n) * (⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊ : ℝ)) ∧
            avgTuples p ⌊(n : ℝ) ^ u⌋₊ (fun a => insec a ⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊) ≤
              (2 / Real.pi) ^ ((1 - o n) * (⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊ : ℝ))) ∧
    (∀ c : ℝ, 1 / 3 < c → c < 1 / 2 → ∀ (m p : ℕ → ℕ) [∀ j, Fact (p j).Prime],
      Tendsto m atTop atTop →
      Tendsto (fun j => Real.log (p j) / ((m j : ℝ) ^ 2 * Real.log (2 * m j))) atTop atTop →
      ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧ ∀ᶠ j : ℕ in atTop,
        avgTuples (p j) (m j) (fun a => delta a ⌊c * m j⌋₊) ≤
            (2 / Real.pi) ^ ((1 - o j) * (⌊c * m j⌋₊ : ℝ)) ∧
          avgTuples (p j) (m j) (fun a => insec a ⌊c * m j⌋₊) ≤
            (2 / Real.pi) ^ ((1 - o j) * (⌊c * m j⌋₊ : ℝ))) := by sorry

end ShamirLLR
