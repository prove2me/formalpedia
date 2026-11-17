-- Prove2me | Theorems.Thm_ShamirLLR_Supplement_theorem_4
-- name    : ShamirLLR.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:25:59.466068+00:00
-- url     : https://prove2.me/theorems/dd9faa80-c67a-49b2-95f3-f546eada5d44
-- title:
--   Theorem 4 — local leakage resilience of Shamir sharing: $\mathbb E_a\,\mathrm{Insec}(a;\lfloor cm\rfloor)\le 2\cdot2^{-d/4}$
-- statement:
--   Let $\mathbb E_a$ be the uniform average over $\mathcal A_{p,m}$ (ordered $m$-tuples of distinct nonzero evaluation places of $\mathbb F_p$) and $\mathrm{Insec}(a;d)$ the one-bit local-leakage insecurity of degree-$d$ Shamir sharing with evaluation places $a$.
--
--   1. Fix $1/3<c<1/2$ and put $d=\lfloor cm\rfloor$. There is a constant $C_c>0$ such that for all sufficiently large $m$ and every odd prime $p$ with $\log p\ge C_c\,m^2\log(2m)$,
--   $$
--   \mathbb E_a\,\mathrm{Insec}(a;d)\le2\cdot2^{-d/4}.
--   $$
--   2. In particular, for fixed $1/3<c<1/2$ and $0<u<1/2$, the same bound holds with $m=\lfloor n^u\rfloor$ for every $n$-bit prime $2^{n-1}<p<2^n$, once $n$ is sufficiently large.
--
--   This is the working local-leakage-resilience bound for Shamir sharing; it follows from Theorem 3 by averaging the pointwise inequality $\mathrm{Insec}(a;d)\le2\Delta(a;d)$ of Eq. (2).
--
--   Differences from the source:
--   - encoding: "Under the hypotheses of Theorem 3" → its own $\exists C_c>0,\ \exists m_0,\ \forall m\ge m_0,\ \forall$ odd prime $p$ with $\log p\ge C_cm^2\log(2m)$; reason: Theorem 3's hypotheses written out; the field-size hypothesis is monotone in $C_c$, so a common constant for Theorems 3 and 4 exists iff each has one
--   - encoding: "odd prime"; "$n$-bit primes" → `[Fact p.Prime]` with `p ≠ 2` in clause 1; prime $p$ with $2^{n-1}<p<2^n$ in clause 2; reason: an $n$-bit prime is odd for $n\ge2$
--   - encoding: "$n$ is sufficiently large", "this holds for $n$-bit primes" → `∀ᶠ n in atTop`, for every prime $2^{n-1}<p<2^n$ with $m=\lfloor n^u\rfloor$; reason: the printed quantifier order, uniformly over the primes
--   - encoding: $\mathbb E_a$ over uniform ordered distinct nonzero tuples → the Finset average `avgTuples p m` over $\mathcal A_{p,m}$ (published `ShamirLLR.evalTuples`); reason: it is $0$ only on an empty $\mathcal A_{p,m}$, which the field-size hypotheses exclude for large $m$ and $n$
--   - encoding: $d=\lfloor cm\rfloor$, $m=\lfloor n^u\rfloor$, $2\cdot2^{-d/4}$, $\log$ → natural floors, real powers, natural logarithm; reason: Lean conventions; $\log$ is natural (p.13)
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Theorem 4, p.5 (PDF p.6); proof p.63 (PDF p.64); bit length $n$, p.2

import Mathlib
import Definitions.Def_ShamirLLR_evalTuples
import Definitions.Def_ShamirLLR_deltaClass
import Definitions.Def_ShamirLLR_insec

set_option autoImplicit false

open Filter Topology

namespace ShamirLLR.Supplement

/-- **Theorem 4 (Local leakage resilience of Shamir sharing).**
1. Under the hypotheses of Theorem 3 (fix `1/3 < c < 1/2`, `d = ⌊cm⌋`; there is `C_c > 0` such
   that for all sufficiently large `m` and every odd prime `p` with `log p ≥ C_c m² log(2m)`),
   `𝔼_a Insec(a; d) ≤ 2 · 2^{−d/4}`.
2. In particular, this holds for `n`-bit primes (`2^{n−1} < p < 2^n`) and `m = ⌊n^u⌋` whenever
   `0 < u < 1/2` is fixed and `n` is sufficiently large.

Source: Hwang–Maji–Shkredov–Ye, *Local Leakage Resilience of Multiplication-friendly Shamir
Secret Sharing*, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…), Theorem 4, p.5;
proof p.63 (from Theorem 3 and Eq. (2)); `n` the bit length of `p`, p.2.

**Formalization Note.** In clause 1, `p` is an odd prime (`[Fact p.Prime]`, `p ≠ 2`), and
`C_c`, `m₀` are existential, chosen after `c` and before `m`, `p`, as in Theorem 3. In clause 2,
`p` is prime (an `n`-bit prime is odd for `n ≥ 2`), `c ∈ (1/3, 1/2)` and `u ∈ (0, 1/2)` are
fixed, and "n sufficiently large" is `∀ᶠ n in atTop`, uniformly over the primes. `d = ⌊cm⌋`,
`m = ⌊n^u⌋` are natural floors; the exponent `−d/4` is real; `log` is natural. -/
theorem theorem_4 :
    (∀ c : ℝ, 1 / 3 < c → c < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
        C * (m : ℝ) ^ 2 * Real.log (2 * m) ≤ Real.log p →
          avgTuples p m (fun a => insec a ⌊c * m⌋₊) ≤
            2 * (2 : ℝ) ^ (-(⌊c * m⌋₊ : ℝ) / 4)) ∧
    (∀ c u : ℝ, 1 / 3 < c → c < 1 / 2 → 0 < u → u < 1 / 2 →
      ∀ᶠ n : ℕ in atTop, ∀ (p : ℕ) [Fact p.Prime], 2 ^ (n - 1) < p → p < 2 ^ n →
        avgTuples p ⌊(n : ℝ) ^ u⌋₊ (fun a => insec a ⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊) ≤
          2 * (2 : ℝ) ^ (-(⌊c * ⌊(n : ℝ) ^ u⌋₊⌋₊ : ℝ) / 4)) := by sorry

end ShamirLLR.Supplement
