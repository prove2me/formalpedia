-- Prove2me | Theorems.Thm_ShamirLLR_Supplement_theorem_3
-- name    : ShamirLLR.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:25:16.042227+00:00
-- url     : https://prove2.me/theorems/c02b6596-f448-45d7-8134-e846c62abd7d
-- title:
--   Theorem 3 — Reed–Solomon pseudorandomness: $\mathbb E_a\,\Delta(a;\lfloor cm\rfloor)\le 2^{-d/4}$ for $1/3<c<1/2$
-- statement:
--   Let $p$ be an odd prime, $\mathbb E_a$ the uniform average over $\mathcal A_{p,m}$ (ordered $m$-tuples of distinct nonzero evaluation places of $\mathbb F_p$), and $\Delta(a;r)$ the distance (1) between one-bit leakage of a uniform Reed–Solomon codeword of $C_r(a)$ and of independent uniform inputs.
--
--   Fix $1/3<c<1/2$ and put $d=\lfloor cm\rfloor$. There is a constant $C_c>0$ such that for all sufficiently large $m$,
--   $$
--   \log p\ge C_c\,m^2\log(2m)\ \Longrightarrow\ \mathbb E_a\big[\Delta(a;d)\big]\le2^{-d/4}.
--   $$
--
--   This is the paper's working bound for Reed–Solomon pseudorandomness, proved in Sections 2–8; it is the input to Theorem 4 and is sharpened to the base $2/\pi$ by Theorem 1.
--
--   Differences from the source:
--   - encoding: "odd prime" (standing assumption, p.1) → `[Fact p.Prime]` with `p ≠ 2`; reason: same primes
--   - encoding: "for all sufficiently large $m$" → a threshold $m_0\in\mathbb N$ chosen after $c$ and $C_c$, before $m$ and $p$; reason: the printed quantifier order
--   - encoding: $\mathbb E_a$ over uniform ordered distinct nonzero tuples → the Finset average `avgTuples p m` over $\mathcal A_{p,m}$ (published `ShamirLLR.evalTuples`); reason: it is $0$ only on an empty $\mathcal A_{p,m}$, which the field-size hypotheses exclude for large $m$ and $n$
--   - encoding: $d=\lfloor cm\rfloor$, $2^{-d/4}$, $\log$ → natural floors, real powers, natural logarithm; reason: Lean conventions; $\log$ is natural (p.13)
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Theorem 3, p.5 (PDF p.6); proof §§2–8, completed p.63 (PDF p.64); odd prime, p.1

import Mathlib
import Definitions.Def_ShamirLLR_evalTuples
import Definitions.Def_ShamirLLR_deltaClass
import Definitions.Def_ShamirLLR_insec

set_option autoImplicit false

namespace ShamirLLR.Supplement

/-- **Theorem 3 (Reed–Solomon pseudorandomness).** Fix `1/3 < c < 1/2` and put `d = ⌊cm⌋`. There
is a constant `C_c > 0` such that for all sufficiently large `m`,
`log p ≥ C_c m² log(2m) ⟹ 𝔼_a [Δ(a; d)] ≤ 2^{−d/4}`, where `a` is uniform over the ordered
distinct nonzero evaluation places (`A_{p,m}`).

Source: Hwang–Maji–Shkredov–Ye, *Local Leakage Resilience of Multiplication-friendly Shamir
Secret Sharing*, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…), Theorem 3, p.5;
proof in §§2–8 (completed p.63).

**Formalization Note.** `p` is an odd prime (standing assumption, p.1): `[Fact p.Prime]` with
`p ≠ 2`. "For all sufficiently large `m`" is a threshold `m₀` chosen after `c` and `C_c` and
before `m` and `p`. `d = ⌊cm⌋` is a natural floor, cast to `ℝ` in the exponent `−d/4` (not
`⌊d/4⌋`); `log` is natural. -/
theorem theorem_3 :
    ∀ c : ℝ, 1 / 3 < c → c < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
        C * (m : ℝ) ^ 2 * Real.log (2 * m) ≤ Real.log p →
          avgTuples p m (fun a => delta a ⌊c * m⌋₊) ≤
            (2 : ℝ) ^ (-(⌊c * m⌋₊ : ℝ) / 4) := by sorry

end ShamirLLR.Supplement
