-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_15
-- name    : PreservePast.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:39:50.969804+00:00
-- url     : https://prove2.me/theorems/e8ebe9e3-dcdd-47fc-862c-256391d3a912
-- title:
--   Theorem 15 — sample-specific information for population prediction
-- statement:
--   In the binary population model with the critical normalization
--   $$\mu_1=\Big(1-\frac1n\Big)^{n-1},\qquad\rho^2d=2\ln(a\mu_1n)-\ln\ln n,\qquad d\ge n^{1/10},\qquad a>1,$$
--   let $X_S$ be the singleton list of the training sample $X$, $P$ the population, $M$ the learner's retained message and $R$ its public coins, and $L^\ast$ the full-sample optimal error.
--
--   1. For every learner of population error at most $L^\ast+\epsilon$,
--   $$I(X_S;M\mid P,R)\ \ge\ \mu_1nd-2nd\epsilon-o(nd),$$
--   with remainder uniform over learners and over $d\ge n^{1/10}$.
--   2. $H(X_S\mid P)=(1+o(1))\mu_1nd$.
--   3. Thus, if $\epsilon=o(1)$,
--   $$I(X_S;M\mid P,R)=(1-o(1))H(X_S\mid P),\qquad I(X;M\mid P,R)\ \ge\ (1-o(1))H(X_S\mid P).$$
--
--   All quantities are in bits.
--
--   **Formalization Note** The model and the quantities are those of `PreservePast.Supplement.binPopData`.
--
--   Differences from the source:
--   - encoding: population error at most L* + ϵ → success at least (1 − L*) − ϵ, with 1 − L* the supremum of the success of full-sample decoders; reason: error is one minus success
--   - encoding: o(nd) uniform over learners and over d ≥ n^{1/10}; statements for sufficiently large n, so 0 < ρ < 1 → for fixed a > 1 a sequence e_n → 0 valid for all admissible (d, ρ), all learners and all ϵ ≥ 0 at each n ≥ 3, with 0 < ρ < 1 a hypothesis; reason: spells out the uniformity; for small n no ρ in (0,1) satisfies the normalization
--   - encoding: if ϵ = o(1), I(X_S; M | P, R) = (1 − o(1))H(X_S | P) and I(X; M | P, R) ≥ (1 − o(1))H(X_S | P) → for every nonnegative ϵ_n → 0 an e_n → 0 such that every learner of error ≤ L* + ϵ_n has (1 − e_n)H ≤ I(X_S; M | P, R) ≤ H and (1 − e_n)H ≤ I(X; M | P, R); reason: a sequence statement; the equality is the two inequalities
--   - encoding: the population P and the singleton data X_S → P is the pattern of fixed class-coordinates with their signs; X_S is the padded singleton list; reason: bijective encodings
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 15, p.57 (PDF p.59), eqs. (191)–(194)

import Mathlib
import Definitions.Def_PreservePast_Supplement_binPopData

open MeasureTheory Filter Topology

namespace PreservePast.Supplement

/-- **Theorem 15 (Sample-specific information for population prediction).** P. Xu, *Information
Required to Preserve Past Learning*, STOC 2027 submission (held version, PDF sha256
48013ceb…d00fa), Theorem 15, p.57 (PDF p.59), eqs. (192)–(194); the model is (191), §K.2, p.57.

In the binary population model with `μ₁ = (1 − 1/n)^{n−1}`, `ρ²d = 2 ln(aμ₁n) − ln ln n`,
`d ≥ n^{1/10}`, `a > 1`: every learner of population error at most `L* + ϵ` has
`I(X_S; M | P, R) ≥ μ₁nd − 2ndϵ − o(nd)` (192), with remainder uniform over learners and over
`d ≥ n^{1/10}`; `H(X_S | P) = (1 + o(1))μ₁nd` (193); and, if `ϵ = o(1)`,
`I(X_S; M | P, R) = (1 − o(1))H(X_S | P)` and `I(X; M | P, R) ≥ (1 − o(1))H(X_S | P)` (194).

**Formalization Note.** `a > 1` is fixed first. Each `o(·)` is a sequence `e_n → 0` valid for
all admissible `(d, ρ)`, all learners and all `ϵ ≥ 0` at each `n ≥ 3`; `0 < ρ < 1` is a
hypothesis ("All statements below concern sufficiently large n, so 0 < ρ < 1"). "Population
error at most `L* + ϵ`" is written with success `= 1 −` error: success `≥ (1 − L*) − ϵ`, where
`1 − L*` is `binPopOptimum`. "If `ϵ = o(1)`" is: for every sequence `ϵ_n → 0` of nonnegative
tolerances there is `e_n → 0` such that every learner of error at most `L* + ϵ_n` satisfies
the two relations of (194) with `1 − e_n`; the equality in (194) is the lower bound together
with `I(X_S; M | P, R) ≤ H(X_S | P)`. Information is an extended nonnegative real, compared
through `ENNReal.ofReal`; all quantities are in bits. -/
theorem theorem_15 :
    ∀ a : ℝ, 1 < a →
      (∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
        ∀ (n : ℕ) [NeZero n] (d : ℕ) (ρ : ℝ), 3 ≤ n → (n : ℝ) ^ ((1 : ℝ) / 10) ≤ d → 0 < ρ → ρ < 1 →
          ρ ^ 2 * d = 2 * Real.log (a * (1 - 1 / (n : ℝ)) ^ (n - 1) * n) - Real.log (Real.log n) →
          (∀ (π : StateProtocol (Fin n → Fin n × (Fin d → Bool)) (Fin d → Bool) (Fin n)) (ε : ℝ),
            0 ≤ ε → binPopOptimum n d ρ - ε ≤ binPopSuccess π ρ →
            ENNReal.ofReal (((1 - 1 / (n : ℝ)) ^ (n - 1) - 2 * ε - e n) * (n * d)) ≤
              binPopSingInfo π ρ) ∧
          |binPopSingEntropy n d ρ - (1 - 1 / (n : ℝ)) ^ (n - 1) * (n * d)| ≤
            e n * ((1 - 1 / (n : ℝ)) ^ (n - 1) * (n * d))) ∧
      ∀ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) → Tendsto ε atTop (𝓝 0) →
        ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
          ∀ (n : ℕ) [NeZero n] (d : ℕ) (ρ : ℝ), 3 ≤ n → (n : ℝ) ^ ((1 : ℝ) / 10) ≤ d → 0 < ρ →
            ρ < 1 →
            ρ ^ 2 * d = 2 * Real.log (a * (1 - 1 / (n : ℝ)) ^ (n - 1) * n) - Real.log (Real.log n) →
            ∀ π : StateProtocol (Fin n → Fin n × (Fin d → Bool)) (Fin d → Bool) (Fin n),
              binPopOptimum n d ρ - ε n ≤ binPopSuccess π ρ →
              ENNReal.ofReal ((1 - e n) * binPopSingEntropy n d ρ) ≤ binPopSingInfo π ρ ∧
              binPopSingInfo π ρ ≤ ENNReal.ofReal (binPopSingEntropy n d ρ) ∧
              ENNReal.ofReal ((1 - e n) * binPopSingEntropy n d ρ) ≤ binPopFullInfo π ρ := by sorry

end PreservePast.Supplement
