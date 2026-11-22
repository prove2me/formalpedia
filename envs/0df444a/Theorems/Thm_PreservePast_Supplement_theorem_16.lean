-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_16
-- name    : PreservePast.Supplement.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:40:48.455994+00:00
-- url     : https://prove2.me/theorems/303f88a8-0141-4707-87f1-5917872fcdb4
-- title:
--   Theorem 16 — Gaussian population memory law
-- statement:
--   In the Gaussian population model, with $p_{0,n}=(1-1/n)^n$, $\mu_n=(1-1/n)^{n-1}$, $b_n=1-p_{0,n}-\mu_n$ and the costs $C_{\rm sing}=I(X_S;M\mid\Theta,R)$, $C_{\rm exc}=I(D;M\mid\Theta,R)$, $C_{\rm tot}=I(D;M\mid R)$ and the fixed register width $W$, let $n\to\infty$, $d\ge n^{1/10}$ and $\rho^2d=2\ln n+\tau_n\sqrt{\ln n}$ with $|\tau_n|\le T$; put $u_n=\Phi(\tau_n/(2\sqrt2))$.
--
--   1. The full-training-data Bayes success is $S^\ast_n=b_n+\mu_nu_n+o(1)$.
--   2. Uniformly over these parameters, every learner with success $S\ge S^\ast_n-\epsilon$, $\epsilon\ge0$, satisfies, in bits,
--   $$C\ \ge\ \Big[\frac14\Big(\mu_n-\frac{\epsilon}{u_n}\Big)_+-e_n\Big]nd\log_2\ln n,\qquad e_n\to0,$$
--   for each $C\in\{C_{\rm sing},C_{\rm exc},C_{\rm tot},W\}$.
--   3. If $\tau_n$ converges and $\epsilon>0$ is fixed, each cost obeys
--   $$\inf_{S\ge S^\ast_n-\epsilon}C=\Big[\frac14\Big(\mu_n-\frac{\epsilon}{u_n}\Big)_++o(1)\Big]nd\log_2\ln n .$$
--   4. Every near-Bayes sequence has leading cost at least $(\mu_n/4-o(1))nd\log_2\ln n$, and a finite-width sequence attains it.
--
--   **Formalization Note** The model and the costs are those of `PreservePast.Supplement.gaussPopData`.
--
--   Differences from the source:
--   - encoding: uniformly over these parameters, o(1) and e_n → 0 → a sequence e_n → 0 chosen after T, valid for all admissible (d, ρ, τ), all learners and all ϵ ≥ 0 at each n ≥ 3; reason: spells out the uniformity; n ≥ 3 makes log₂ ln n positive
--   - encoding: 0 < ρ < 1 is not repeated in the theorem → the hypothesis 0 < ρ < 1; reason: both √ρ and √(1 − ρ) occur in the model
--   - encoding: inf over learners of success ≥ S*_n − ϵ of each cost, for convergent τ_n and fixed ϵ > 0 → parameters d_n, ρ_n, τ_n as functions of n with τ_n convergent; every learner of success ≥ S*_n − ϵ has each cost ≥ [¼(μ_n − ϵ/u_n)₊ − e_n]nd log₂ ln n, and from some n on one learner of success ≥ S*_n − ϵ has all four costs ≤ [¼(μ_n − ϵ/u_n)₊ + e_n]nd log₂ ln n; reason: two-part form of a least cost; avoids junk values of infima
--   - reading: Every near-Bayes sequence has leading cost at least (μ_n/4 − o(1))nd log₂ ln n, and a finite-width sequence attains it → uniformly over all admissible parameters (no convergence of τ_n): for every ϵ_n → 0 an e_n → 0 with all four costs ≥ (μ_n/4 − e_n)nd log₂ ln n for learners of success ≥ S*_n − ϵ_n, and an e_n → 0 with a finite-width learner of success ≥ S*_n − e_n and width ≤ (μ_n/4 + e_n)nd log₂ ln n; reason: the sentence does not say whether convergence of τ_n is still assumed; the uniform form implies the form along every sequence
--   - encoding: S*_n, the full-training-data Bayes success, and X_S, the singleton observations in training order → the supremum of the success of jointly measurable decoders of (D, query); the padded singleton list; reason: randomizing the decoder cannot increase the optimum; a bijective encoding of the list
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 16, p.58 (PDF p.60), eqs. (201)–(202); §K.3, p.58

import Mathlib
import Definitions.Def_PreservePast_Supplement_IdProtocol
import Definitions.Def_PreservePast_Supplement_gaussPopData

open MeasureTheory Filter Topology

namespace PreservePast.Supplement

/-- **Theorem 16 (Gaussian population memory law).** P. Xu, *Information Required to Preserve
Past Learning*, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), Theorem 16, p.58
(PDF p.60), eqs. (201)–(202); the model is that of §K.3, p.58.

Let `n → ∞`, `d ≥ n^{1/10}`, `ρ²d = 2 ln n + τ_n√(ln n)`, `|τ_n| ≤ T`, `u_n = Φ(τ_n/(2√2))`,
and `p_{0,n} = (1 − 1/n)^n`, `μ_n = (1 − 1/n)^{n−1}`, `b_n = 1 − p_{0,n} − μ_n`. The
full-training-data Bayes success is `S*_n = b_n + μ_n u_n + o(1)`. Uniformly over these
parameters, every learner with success `S ≥ S*_n − ϵ`, `ϵ ≥ 0`, has
`C ≥ [¼(μ_n − ϵ/u_n)₊ − e_n] nd log₂ ln n`, `e_n → 0`, for each
`C ∈ {C_sing, C_exc, C_tot, W}` (201). If `τ_n` converges and `ϵ > 0` is fixed, each cost obeys
`inf_{S ≥ S*_n − ϵ} C = [¼(μ_n − ϵ/u_n)₊ + o(1)] nd log₂ ln n` (202). Every near-Bayes sequence
has leading cost at least `(μ_n/4 − o(1)) nd log₂ ln n`, and a finite-width sequence attains it.

**Formalization Note.** `0 < ρ < 1` (both `√ρ` and `√(1−ρ)` occur in the model). Each `o(1)` or
`e_n` is a sequence `e_n → 0`, chosen after `T` only, valid for all admissible `(d, ρ, τ)`, all
learners and all `ϵ ≥ 0` at each `n ≥ 3` (so that `log₂ ln n > 0`). The first block is the Bayes
success and (201). The second block is (202) for parameters `d_n, ρ_n, τ_n` given as functions of
`n` with `τ_n → τ₀`: for each cost the lower bound for every learner of success `≥ S*_n − ϵ`,
and, from some `n` on, one learner of success `≥ S*_n − ϵ` whose width and three informations
are all at most `[¼(μ_n − ϵ/u_n)₊ + e_n] nd log₂ ln n`. The third block is the last sentence:
for every `ϵ_n → 0` there is `e_n → 0` such that learners of success `≥ S*_n − ϵ_n` have all
four costs `≥ (μ_n/4 − e_n) nd log₂ ln n`; and there is `e_n → 0` and, for all admissible
parameters, a finite-width learner of success `≥ S*_n − e_n` and width
`≤ (μ_n/4 + e_n) nd log₂ ln n`. `W` is the width of a fixed register (`HasWidth`). Information
is an extended nonnegative real, compared through `ENNReal.ofReal`; all costs are in bits. -/
theorem theorem_16 :
    (∀ T : ℝ, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ (n : ℕ) [NeZero n] (d : ℕ) (ρ τ : ℝ), 3 ≤ n → (n : ℝ) ^ ((1 : ℝ) / 10) ≤ d → 0 < ρ →
        ρ < 1 → |τ| ≤ T → ρ ^ 2 * d = 2 * Real.log n + τ * Real.sqrt (Real.log n) →
        |gaussPopOptimum n d ρ - ((1 - (1 - 1 / (n : ℝ)) ^ n - (1 - 1 / (n : ℝ)) ^ (n - 1)) +
            (1 - 1 / (n : ℝ)) ^ (n - 1) * stdNormalCdf (τ / (2 * Real.sqrt 2)))| ≤ e n ∧
        ∀ (π : StateProtocol (Fin n → Fin n × (Fin d → ℝ)) (Fin d → ℝ) (Fin n)) (ε : ℝ),
          0 ≤ ε → gaussPopOptimum n d ρ - ε ≤ gaussPopSuccess π ρ →
          ENNReal.ofReal ((1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
              ε / stdNormalCdf (τ / (2 * Real.sqrt 2))) 0 - e n) *
              (n * d * Real.logb 2 (Real.log n))) ≤ gaussPopSing π ρ ∧
          ENNReal.ofReal ((1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
              ε / stdNormalCdf (τ / (2 * Real.sqrt 2))) 0 - e n) *
              (n * d * Real.logb 2 (Real.log n))) ≤ gaussPopExc π ρ ∧
          ENNReal.ofReal ((1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
              ε / stdNormalCdf (τ / (2 * Real.sqrt 2))) 0 - e n) *
              (n * d * Real.logb 2 (Real.log n))) ≤ gaussPopTot π ρ ∧
          ∀ W : ℕ, π.HasWidth W →
            (1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
              ε / stdNormalCdf (τ / (2 * Real.sqrt 2))) 0 - e n) *
              (n * d * Real.logb 2 (Real.log n)) ≤ (W : ℝ)) ∧
    (∀ (T τ₀ : ℝ) (d : ℕ → ℕ) (ρ τ : ℕ → ℝ),
      (∀ n : ℕ, 3 ≤ n → (n : ℝ) ^ ((1 : ℝ) / 10) ≤ d n ∧ 0 < ρ n ∧ ρ n < 1 ∧ |τ n| ≤ T ∧
        ρ n ^ 2 * d n = 2 * Real.log n + τ n * Real.sqrt (Real.log n)) →
      Tendsto τ atTop (𝓝 τ₀) →
      ∀ ε : ℝ, 0 < ε →
        ∃ (e : ℕ → ℝ) (n₀ : ℕ), Tendsto e atTop (𝓝 0) ∧ ∀ (n : ℕ) [NeZero n], n₀ ≤ n → 3 ≤ n →
          (∀ π : StateProtocol (Fin n → Fin n × (Fin (d n) → ℝ)) (Fin (d n) → ℝ) (Fin n),
            gaussPopOptimum n (d n) (ρ n) - ε ≤ gaussPopSuccess π (ρ n) →
            ENNReal.ofReal ((1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
                ε / stdNormalCdf (τ n / (2 * Real.sqrt 2))) 0 - e n) *
                (n * d n * Real.logb 2 (Real.log n))) ≤ gaussPopSing π (ρ n) ∧
            ENNReal.ofReal ((1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
                ε / stdNormalCdf (τ n / (2 * Real.sqrt 2))) 0 - e n) *
                (n * d n * Real.logb 2 (Real.log n))) ≤ gaussPopExc π (ρ n) ∧
            ENNReal.ofReal ((1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
                ε / stdNormalCdf (τ n / (2 * Real.sqrt 2))) 0 - e n) *
                (n * d n * Real.logb 2 (Real.log n))) ≤ gaussPopTot π (ρ n) ∧
            ∀ W : ℕ, π.HasWidth W →
              (1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
                ε / stdNormalCdf (τ n / (2 * Real.sqrt 2))) 0 - e n) *
                (n * d n * Real.logb 2 (Real.log n)) ≤ (W : ℝ)) ∧
          ∃ (π : StateProtocol (Fin n → Fin n × (Fin (d n) → ℝ)) (Fin (d n) → ℝ) (Fin n))
            (W : ℕ), π.HasWidth W ∧ gaussPopOptimum n (d n) (ρ n) - ε ≤ gaussPopSuccess π (ρ n) ∧
            (W : ℝ) ≤ (1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
                ε / stdNormalCdf (τ n / (2 * Real.sqrt 2))) 0 + e n) *
                (n * d n * Real.logb 2 (Real.log n)) ∧
            gaussPopSing π (ρ n) ≤ ENNReal.ofReal ((1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
                ε / stdNormalCdf (τ n / (2 * Real.sqrt 2))) 0 + e n) *
                (n * d n * Real.logb 2 (Real.log n))) ∧
            gaussPopExc π (ρ n) ≤ ENNReal.ofReal ((1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
                ε / stdNormalCdf (τ n / (2 * Real.sqrt 2))) 0 + e n) *
                (n * d n * Real.logb 2 (Real.log n))) ∧
            gaussPopTot π (ρ n) ≤ ENNReal.ofReal ((1 / 4 * max ((1 - 1 / (n : ℝ)) ^ (n - 1) -
                ε / stdNormalCdf (τ n / (2 * Real.sqrt 2))) 0 + e n) *
                (n * d n * Real.logb 2 (Real.log n)))) ∧
    ∀ T : ℝ,
      (∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
        ∀ (n : ℕ) [NeZero n] (d : ℕ) (ρ τ : ℝ), 3 ≤ n → (n : ℝ) ^ ((1 : ℝ) / 10) ≤ d → 0 < ρ →
          ρ < 1 → |τ| ≤ T → ρ ^ 2 * d = 2 * Real.log n + τ * Real.sqrt (Real.log n) →
          ∀ π : StateProtocol (Fin n → Fin n × (Fin d → ℝ)) (Fin d → ℝ) (Fin n),
            gaussPopOptimum n d ρ - ε n ≤ gaussPopSuccess π ρ →
            ENNReal.ofReal (((1 - 1 / (n : ℝ)) ^ (n - 1) / 4 - e n) *
                (n * d * Real.logb 2 (Real.log n))) ≤ gaussPopSing π ρ ∧
            ENNReal.ofReal (((1 - 1 / (n : ℝ)) ^ (n - 1) / 4 - e n) *
                (n * d * Real.logb 2 (Real.log n))) ≤ gaussPopExc π ρ ∧
            ENNReal.ofReal (((1 - 1 / (n : ℝ)) ^ (n - 1) / 4 - e n) *
                (n * d * Real.logb 2 (Real.log n))) ≤ gaussPopTot π ρ ∧
            ∀ W : ℕ, π.HasWidth W →
              ((1 - 1 / (n : ℝ)) ^ (n - 1) / 4 - e n) * (n * d * Real.logb 2 (Real.log n)) ≤
                (W : ℝ)) ∧
      ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
        ∀ (n : ℕ) [NeZero n] (d : ℕ) (ρ τ : ℝ), 3 ≤ n → (n : ℝ) ^ ((1 : ℝ) / 10) ≤ d → 0 < ρ →
          ρ < 1 → |τ| ≤ T → ρ ^ 2 * d = 2 * Real.log n + τ * Real.sqrt (Real.log n) →
          ∃ (π : StateProtocol (Fin n → Fin n × (Fin d → ℝ)) (Fin d → ℝ) (Fin n)) (W : ℕ),
            π.HasWidth W ∧ gaussPopOptimum n d ρ - e n ≤ gaussPopSuccess π ρ ∧
            (W : ℝ) ≤ ((1 - 1 / (n : ℝ)) ^ (n - 1) / 4 + e n) *
              (n * d * Real.logb 2 (Real.log n)) := by sorry

end PreservePast.Supplement
