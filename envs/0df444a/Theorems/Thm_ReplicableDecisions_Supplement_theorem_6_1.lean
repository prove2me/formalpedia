-- Prove2me | Theorems.Thm_ReplicableDecisions_Supplement_theorem_6_1
-- name    : ReplicableDecisions.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:07:46.417958+00:00
-- url     : https://prove2.me/theorems/286bf1fb-93db-443e-ad06-c2c6388fb614
-- title:
--   Theorem 6.1 — a logarithmic separation at constant chain scale
-- statement:
--   There are universal constants $C_1,C_2>0$ such that for every integer $b\ge1$ there is a rational experiment with $M=2^b$ models, two outputs and no indifference models (every acceptable set is $\{0\}$ or $\{1\}$, and both occur), such that
--   $$s_L=\sqrt{1-2^{-1/2}}\qquad\text{for every }L\ge1,$$
--   and for $0<\beta\le1/8$ and $0<\rho\le1/16$,
--   $$n^\star(\beta,\rho)\ge\max\Big\{b,\ \log_2\frac{1-\beta}\beta,\ \log_2\frac{2(1-2\beta)}\rho\Big\},\qquad n^\star(\beta,\rho)\le\Big\lceil\log_2\frac{2^b-1}{\min\{\beta,\rho/2\}}\Big\rceil,$$
--   and $C_1\log(M/\min\{\beta,\rho\})\le n^\star(\beta,\rho)\le C_2\log(M/\min\{\beta,\rho\})$.
--
--   The chain scale is constant while the optimal sample size grows like $\log M$: the logarithm of Theorem 3.1 can be necessary.
--
--   Differences from the source:
--   - encoding: "rational experiment", "two outputs", "no indifference models" → every table entry equals a rational number; Y = Bool; every Γ i is {false} or {true}; reason: literal Lean readings
--   - reading: no indifference models, s_L defined → also asserts both forced classes nonempty; reason: s_L is defined only with both forced classes nonempty; the construction has P∗ forced 0 and P_u forced 1
--   - encoding: Θ(log(M/min{β, ρ})) "with universal constants" → ∃ C₁ C₂ > 0 before b with C₁ log(M/min{β, ρ}) ≤ N ≤ C₂ log(M/min{β, ρ}); reason: the Lean reading of Θ
--   - encoding: n⋆(β, ρ) = min{n : a (β, ρ)-valid n-sample algorithm exists} → the least element N of the published validSampleSizes (IsLeast); reason: a minimum read without sInf junk values; the theorem asserts it exists
--   - encoding: √(1 − 2^{−1/2}), log₂ → Real.sqrt (1 − 1/√2), Real.logb 2; reason: the same numbers
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Theorem 6.1, (6.1)–(6.2), p.26 (PDF p.28)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid
import Definitions.Def_ReplicableDecisions_hopSeparation

namespace ReplicableDecisions.Supplement

/-- **Theorem 6.1 (A logarithmic separation).** Chen, *Replicable Decisions in Finite Experiments*,
STOC 2027 submission (sha256 52d181db…), Theorem 6.1, (6.1)–(6.2), p.26 (PDF p.28). For every
integer `b ≥ 1` there is a rational experiment with `M = 2^b` models, two outputs, and no
indifference models, such that `s_L = √(1 − 2^{−1/2})` for every `L ≥ 1`. For `0 < β ≤ 1/8` and
`0 < ρ ≤ 1/16`, `n⋆(β, ρ) ≥ max{b, log₂((1 − β)/β), log₂(2(1 − 2β)/ρ)}` and
`n⋆(β, ρ) ≤ ⌈log₂((2^b − 1)/min{β, ρ/2})⌉`. Consequently `n⋆(β, ρ) = Θ(log(M/min{β, ρ}))` with
universal constants.

**Formalization Note.** "Rational": every table entry is a rational number. "Two outputs":
`Y = Bool`. "No indifference models": every `Γ(P)` is `{0}` or `{1}`; both forced classes are also
asserted nonempty. `2^{−1/2} = 1/√2`. The two universal constants are quantified before `b`. -/
theorem theorem_6_1 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ b : ℕ, 1 ≤ b →
      ∃ (ι : Type) (_ : Fintype ι) (Z : Type) (_ : Fintype Z) (E : Experiment ι Z)
        (Γ : ι → Set Bool),
        (∀ i z, ∃ q : ℚ, E.P i z = q) ∧ Fintype.card ι = 2 ^ b ∧
        (∀ i, Γ i = {false} ∨ Γ i = {true}) ∧
        (forcedClass Γ false).Nonempty ∧ (forcedClass Γ true).Nonempty ∧
        (∀ L : ℕ, 1 ≤ L → hopSeparation E Γ L = Real.sqrt (1 - 1 / Real.sqrt 2)) ∧
        ∀ β ρ : ℝ, 0 < β → β ≤ 1 / 8 → 0 < ρ → ρ ≤ 1 / 16 →
          ∃ N : ℕ, IsLeast (validSampleSizes E Γ β ρ) N ∧
            max (b : ℝ) (max (Real.logb 2 ((1 - β) / β)) (Real.logb 2 (2 * (1 - 2 * β) / ρ)))
              ≤ (N : ℝ) ∧
            N ≤ ⌈Real.logb 2 (((2 : ℝ) ^ b - 1) / min β (ρ / 2))⌉₊ ∧
            C₁ * Real.log ((Fintype.card ι : ℝ) / min β ρ) ≤ (N : ℝ) ∧
            (N : ℝ) ≤ C₂ * Real.log ((Fintype.card ι : ℝ) / min β ρ) := by sorry

end ReplicableDecisions.Supplement
