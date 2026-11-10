-- Prove2me | Theorems.Thm_ThinShellSampling_proposition_6_5
-- name    : ThinShellSampling.proposition_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:49:03.939218+00:00
-- url     : https://prove2.me/theorems/30244017-66ba-4ced-8205-df9cf13ccddf
-- title:
--   Proposition 6.5 — the lifted annealing sampler $\mathsf{PS}_{\mathrm{ann}}$
-- statement:
--   Under the standing assumptions of §6, let $\mu=\mu_{\sigma^2,\rho}$ with $\sigma^2\ge1/n$, $1\le\rho\le n$, and let $\varepsilon\in(0,1)$, $\eta\in(0,1/2)$, $q\ge q_0\ge2$. Let $\mu_0\ll\mu$ be an initial law with $M_{q_0}=\|d\mu_0/d\mu\|_{L^{q_0}(\mu)}\le10$ and $M_2=\|d\mu_0/d\mu\|_{L^2(\mu)}$, and let $M_2\le\bar M\le10$. There are universal constants $C,k,C',k',C_2$ such that, with
--
--   $$
--   A=n^2(\sigma^2\vee1)\log\tfrac q\varepsilon\log\tfrac1\eta,\quad N=\big\lceil C A\log^k(2+A)\big\rceil,\quad S=\frac{16N\bar M}{\eta},\quad h=\frac{1}{1200^2n^2\log S},\quad \tau=2S^2\log^2S,
--   $$
--
--   running one attempt of $\mathsf{PS}_{\mathrm{ann}}$ for $N$ iterations from $z_0\sim\mu_0$ with step size $h$ and at most $\lfloor\tau\rfloor$ rejection trials per step:
--
--   1. $q_0\ge2\vee C_2\log(N/\eta)$ implies $q_0\ge1+\log\tau$;
--   2. if $q_0\ge1+\log\tau$, then with probability at least $1-\eta$ the attempt completes all $N$ iterations; conditioned on this event its output law $\nu$ satisfies $\mathsf R_q(\nu\,\|\,\mu)\le\varepsilon+2\log\frac1{1-\eta}$; the expected number of evaluation queries is at most $C'A'\log^{k'}(2+A')$ with $A'=n^2(\sigma^2\vee1)\log\frac q\varepsilon\log^2\frac1\eta$; and the uncapped chain ($\tau=\infty$) has output law $\bar\nu$ with $\mathsf R_q(\bar\nu\,\|\,\mu)\le\varepsilon$.
--
--   Each phase of Algorithm 6.6 is one call of this sampler.
--
--   **Formalization Note** The attempt is the oracle program `psAnnAttempt`, run on the product of $\mu_0$ and the uniform stream; the output map, the success event and the query count are asserted to be a.e.-measurable.
--
--   Differences from the source:
--
--   - generalization: S = 16NM₂/η → S = 16N·M̄/η for every M̄ with M₂ ≤ M̄ ≤ 10; reason: M̄ = M₂ is the printed choice and M̄ = 10 is the choice S = 160N/η made in Algorithm 6.6
--   - reading: N = Õ(n²(σ² ∨ 1) log(q/ε) log(1/η)) iterations; Õ(n²(σ² ∨ 1) log(q/ε) log²(1/η)) queries → N = ⌈C·A·log(2 + A)^k⌉ and expected queries ≤ C'·A'·log(2 + A')^{k'} with universal C, k, C', k'; reason: §1.3, p.12: a = Õ(b) means a = O(b polylog b)
--   - reading: "using Õ(…) evaluation queries in expectation" (after "Conditioned on this event") → the unconditional expected number of queries of one attempt; reason: the quantity the proof bounds (E C ≤ Σ E C_i, p.17); the conditional expectation is at most (1 − η)⁻¹ ≤ 2 times it
--   - reading: "The latter condition is ensured by q₀ ≥ 2 ∨ O(log(N/η))" → ∃ universal C₂: max(2, C₂ log(N/η)) ≤ q₀ implies 1 + log τ ≤ q₀; reason: O(·) is a universal constant
--   - reading: PS_ann run with threshold τ and initial distribution µ₀ → the oracle program psAnnAttempt with ⌊τ⌋ trials, on the product law µ₀ ⊗ (uniform stream), with the output map, success event and query count asserted a.e.-measurable; reason: "exceeds τ trials" allows ⌊τ⌋ trials; the a.e.-measurability makes the probability and law statements meaningful
--   - encoding: M_{q₀} ≤ 10 → µ₀ ≪ µ and ‖dµ₀/dµ‖_{L^{q₀}(µ)} ≤ 10; reason: a finite warmness presupposes absolute continuity
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Proposition 6.5, p.39 (PDF p.41); §6.3.1, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_ThinShellSampling_renyi
import Definitions.Def_ThinShellSampling_muAnneal
import Definitions.Def_ThinShellSampling_Prog
import Definitions.Def_ThinShellSampling_psAnnAttempt

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Proposition 6.5 (Lifted annealing sampler).**

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), Proposition 6.5, p.39 (PDF p.41): "Let `µ = µ_{σ²,ρ}` be as in (6.1) with `σ² ≥ 1/n` and
`1 ≤ ρ ≤ n`. Given access to an evaluation oracle for `V`, let `ε ∈ (0, 1)`, `η ∈ (0, 1/2)`, `q ≥ q₀ ≥ 2`,
and let `µ₀` be an initial distribution with `M_{q₀} := ‖dµ₀/dµ‖_{L^{q₀}(µ)}`. Initialize `PS_ann` from `µ₀`
and iterate it `N = Õ(n²(σ² ∨ 1) log(q/ε) log(1/η))` times with `h = (1200²n² log S)⁻¹` and
`τ = 2S² log² S`, where `S = 16NM₂/η`. Assume `M_{q₀} ≤ 10` and `q₀ ≥ 1 + log τ`.
• The latter condition is ensured by `q₀ ≥ 2 ∨ O(log(N/η))`.
• With probability at least `1 − η`, `PS_ann` completes all `N` iterations without failure. Conditioned on
this event, its output law `ν` satisfies `R_q(ν ‖ µ) ≤ ε + 2 log 1/(1 − η)`, using
`Õ(n²(σ² ∨ 1) log(q/ε) log²(1/η))` evaluation queries in expectation. The corresponding uncapped chain
(i.e., `τ = ∞`) has output law `ν̄` satisfying `R_q(ν̄ ‖ µ) ≤ ε`."

**Formalization Note.**
* `Õ(A)` iterations: `N = ⌈C·A·log(2 + A)^k⌉` with `A = n²(σ² ∨ 1) log(q/ε) log(1/η)` and constants
  `C, k` chosen before every instance; the query bound is `C'·A'·log(2 + A')^{k'}` with
  `A' = n²(σ² ∨ 1) log(q/ε) log²(1/η)`. `O(log(N/η))` is `C₂ log(N/η)` with `C₂` universal.
* `S = 16 N M̄/η` for any `M̄` with `M₂ ≤ M̄ ≤ 10`: `M̄ = M₂` is the printed choice, and `M̄ = 10` is the
  choice `S = 160N/η` of Algorithm 6.6.
* One attempt of `PS_ann` is the oracle program `psAnnAttempt` (rejection trials capped at `⌊τ⌋`). Its
  initial point `z₀ ∼ µ₀` is independent of the random stream `ω`, so the attempt is run on the product
  law `µ₀ ⊗ streamMeasure`. "With probability at least `1 − η`" is `P(success) ≥ 1 − η`; `ν` is the
  conditional law of the output given success; the expected number of queries is the unconditional
  expectation over one attempt (the quantity the proof bounds; the conditional one is at most
  `(1 − η)⁻¹` times it). The output map, success event and query count are asserted to be
  a.e.-measurable.
* The uncapped chain is `psAnnIdeal`, the exact proximal sampler for `µ`.
* `M_{q₀} ≤ 10` presupposes `µ₀ ≪ µ`, which is stated. The truncation uses `R = Rrad V`. -/
theorem proposition_6_5 :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ C' : ℝ, 0 < C' ∧ ∃ k' : ℕ, ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ V : EuclideanSpace ℝ (Fin n) → WithTop ℝ, IsStandardPotential V →
    ∀ (σ2 ρ ε η q q₀ Mbar : ℝ) (μ₀ : Measure (EuclideanSpace ℝ (Fin n) × ℝ))
      [IsProbabilityMeasure μ₀],
      1 / (n : ℝ) ≤ σ2 → 1 ≤ ρ → ρ ≤ n → 0 < ε → ε < 1 → 0 < η → η < 1 / 2 →
      2 ≤ q₀ → q₀ ≤ q →
      let μ := muAnneal V (Rrad V) σ2 ρ
      μ₀ ≪ μ →
      eLpNorm (fun z => (μ₀.rnDeriv μ z).toReal) (ENNReal.ofReal q₀) μ ≤ 10 →
      eLpNorm (fun z => (μ₀.rnDeriv μ z).toReal) 2 μ ≤ ENNReal.ofReal Mbar → Mbar ≤ 10 →
      let A : ℝ := (n : ℝ) ^ 2 * max σ2 1 * Real.log (q / ε) * Real.log (1 / η)
      let A' : ℝ := (n : ℝ) ^ 2 * max σ2 1 * Real.log (q / ε) * Real.log (1 / η) ^ 2
      let N : ℕ := ⌈C * A * Real.log (2 + A) ^ k⌉₊
      let S : ℝ := 16 * N * Mbar / η
      let h : ℝ := 1 / (1200 ^ 2 * (n : ℝ) ^ 2 * Real.log S)
      let τ : ℝ := 2 * S ^ 2 * Real.log S ^ 2
      let attempt : EuclideanSpace ℝ (Fin n) × ℝ → Prog n (Option (EuclideanSpace ℝ (Fin n) × ℝ)) :=
        psAnnAttempt n (aConst V) (Drad (Rrad V)) bConst σ2 ρ h ⌊τ⌋₊ N
      let P : Measure ((EuclideanSpace ℝ (Fin n) × ℝ) × (ℕ → unitInterval)) :=
        μ₀.prod streamMeasure
      let out : (EuclideanSpace ℝ (Fin n) × ℝ) × (ℕ → unitInterval) →
          Option (EuclideanSpace ℝ (Fin n) × ℝ) := fun p => output none V (attempt p.1) p.2
      let succ : Set ((EuclideanSpace ℝ (Fin n) × ℝ) × (ℕ → unitInterval)) :=
        {p | (out p).isSome}
      let ν : Measure (EuclideanSpace ℝ (Fin n) × ℝ) :=
        (P succ)⁻¹ • (P.restrict succ).map (fun p => (out p).getD 0)
      (max 2 (C₂ * Real.log (N / η)) ≤ q₀ → 1 + Real.log τ ≤ q₀) ∧
      (1 + Real.log τ ≤ q₀ →
        (AEMeasurable (fun p => (out p).getD 0) P ∧ NullMeasurableSet succ P ∧
          AEMeasurable (fun p => queryCount V (attempt p.1) p.2) P) ∧
        ENNReal.ofReal (1 - η) ≤ P succ ∧
        renyi q ν μ ≤ ENNReal.ofReal (ε + 2 * Real.log (1 / (1 - η))) ∧
        (∫⁻ p, (queryCount V (attempt p.1) p.2 : ℝ≥0∞) ∂P) ≤
          ENNReal.ofReal (C' * A' * Real.log (2 + A') ^ k') ∧
        renyi q (psAnnIdeal μ h N μ₀) μ ≤ ENNReal.ofReal ε) := by sorry

end ThinShellSampling
