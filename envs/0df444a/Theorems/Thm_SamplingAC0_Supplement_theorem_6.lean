-- Prove2me | Theorems.Thm_SamplingAC0_Supplement_theorem_6
-- name    : SamplingAC0.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:41:26.395284+00:00
-- url     : https://prove2.me/theorems/3c91b507-d27b-42c0-9305-e434b04a5728
-- title:
--   Theorem 6 — $d$-local cell-probe samplers are at distance $1-\log^{c^d}n/\sqrt n$ from a Hamming slice
-- statement:
--   There are absolute constants $c_1,c_2>0$ with the following property. Let $n\ge c_1$ and let $k$ satisfy $0.1n\le k\le 0.9n$; let $D\sim\binom{[n]}{k}$ be the uniform distribution on the strings in $\{0,1\}^n$ of Hamming weight $k$. Let $s,d\ge 0$ and let $f:[n]^s\to\{0,1\}^n$ be $d$-local, i.e. each output bit depends on at most $d$ of the $s$ input cells, each cell holding an element of $[n]$. Then, for $U$ uniform on $[n]^s$,
--   $$\Delta\bigl(f(U),D\bigr)\;\ge\;1-\frac{(\log_2 n)^{c_2^{\,d}}}{\sqrt n}.$$
--   The constants do not depend on $n$, $k$, $s$, $d$ or $f$.
--
--   Since a cell holds $\log n$ bits, the theorem shows that non-adaptive cell-probe samplers, and hence non-adaptive succinct membership data structures for $k$-subsets of $[n]$, need logarithmic redundancy.
--
--   **Formalization Note** The exponent is $c^d$, as printed (the $d$ is a superscript of $c$). Locality counts input cells, and the number $s$ of cells is arbitrary. The typeclass assumption $n\neq0$ makes $[n]^s$ carry a uniform distribution; it follows from $n\ge c_1>0$.
--
--   Differences from the source:
--   - reading: $\log n$ with unspecified base → $\log_2 n$; reason: base 2 is the paper's convention (p.15 "logarithms in base two"); a different base changes $\log n$ by a constant factor, which the constants absorb for $n\ge c_1$
--   - encoding: $n\ge c$ → $n\ge c_1$ together with the typeclass assumption $n\neq 0$; reason: $n\neq0$ follows from $n\ge c_1>0$ and only lets Lean form the uniform distribution on $[n]^s$
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 6, p.4 (proof §6, pp.16–20)

import Mathlib
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_Supplement_IsLocal
import Definitions.Def_SamplingAC0_Supplement_cellLaw
import Definitions.Def_SamplingAC0_Supplement_slice
set_option autoImplicit false

namespace SamplingAC0.Supplement

/-- **Theorem 6 (Hamming slices against non-adaptive cell probes).** Riazanov–Viola, *Sampling
Tools and the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 6, p.4
(proof §6, pp.16–20): "Let D ∼ ([n] choose k) where n ≥ c and 0.1n ≤ k ≤ 0.9n. Let
f : [n]^s → {0, 1}^n be a d-local function. Then ∆(f(U), D) ≥ 1 − log^{c^d} n / √n."

**Formalization Note.**
* c-notation (p.2): the two occurrences of `c` are absolute positive constants `c₁` (in `n ≥ c₁`)
  and `c₂` (the base of the exponent `c₂^d`), chosen before `n`, `k`, `s`, `d` and `f`; neither
  depends on `d`. The exponent is `c^d` (the `d` is a superscript of `c` on the page, and the proof,
  p.20, bounds `t ≤ (A log n)^{C^d}`).
* The input is `s` cells with values in `[n] = Fin n` (cells of `log n` bits); `U` is uniform on
  `[n]^s`; `d`-locality counts input cells (`IsLocal` over the alphabet `Fin n`). `s` and `d` are
  arbitrary naturals.
* `n ≠ 0` is a typeclass argument so that `[n]^s` carries a uniform distribution; it follows from
  `n ≥ c₁ > 0`.
* `log` is base 2. `0.1n ≤ k ≤ 0.9n` is compared over the reals. -/
theorem theorem_6 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (n : ℕ) [NeZero n], c₁ ≤ (n : ℝ) →
      ∀ k : ℕ, (0.1 : ℝ) * n ≤ k → (k : ℝ) ≤ (0.9 : ℝ) * n →
      ∀ (s d : ℕ) (f : (Fin s → Fin n) → (Fin n → Bool)), IsLocal d f →
        1 - Real.logb 2 n ^ (c₂ ^ d) / Real.sqrt n ≤
          SamplingAC0.tvDist (cellLaw f) (slice n k) := by sorry

end SamplingAC0.Supplement
