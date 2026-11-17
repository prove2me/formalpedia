-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_7_2
-- name    : TightQLB.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:26:38.579593+00:00
-- url     : https://prove2.me/theorems/a2b594ed-9917-4d9f-8adf-8d6f6081df80
-- title:
--   Theorem 7.2 — certified randomness from Fourier sampling: $H^\eta_{\min}(Z\mid RE)\ge n-4\log q-\log(n+2)-3-2\log\frac1{1-\eta_0}$
-- statement:
--   Let $N=2^n$ with $n\ge1$, $q\ge1$ and $\delta\ge0$, and consider an experiment in the Fourier ensemble (Definition 3.1, with an adversary Eve holding a register $E$ and learning the oracle $f$ afterwards) in which the device makes at most $q$ queries and has expected score $B(\mathcal A)\ge3-2/N-\delta$. Put
--
--   $$
--   \bar\lambda_q=\frac2{\sqrt N}\sum_{t=0}^{q-1}\sqrt t,\qquad \eta_0=\bar\lambda_q+\Big(\frac{\delta}{2(1-1/N)}+\frac{\bar\lambda_q}{1-1/N}+\bar\lambda_q^2\Big)^{1/2}.
--   $$
--
--   If $\eta_0<1$, then for every $\eta\in[\eta_0,1]$ the smooth min-entropy of the output given Eve's register and the oracle satisfies
--
--   $$
--   H^\eta_{\min}(Z\mid RE)_\rho\ge n-4\log q-\log(n+2)-3-2\log\frac1{1-\eta_0}.
--   $$
--
--   Moreover $\bar\lambda_1=0$ and $\eta_0\le\sqrt\delta+2q^{3/4}N^{-1/4}+3q^{3/2}N^{-1/2}$. Logarithms are to base 2.
--
--   A device that nearly attains the ideal score with few queries must therefore output almost $n$ bits of randomness that Eve cannot predict, even knowing $f$ and holding an entangled register.
--
--   **Formalization Note** $\rho$ is the family $f\mapsto(\rho^f_z)_z$ of Eve's conditional states of the base mission's experiment, over the uniform law of $f$.
--
--   Differences from the source:
--   - reading: the operational experiment of Definition 3.1 (record, adaptive operations, at most q queries along every path) → a density matrix on A × E, q + 1 oracle-independent CPTP rounds on A, q controlled queries between them and a POVM, as in the base mission's TightQLB.Experiment; reason: the proof of Lemma 3.2, Steps 1–2, puts every experiment in this form and conversely every such channel form is an experiment of Definition 3.1
--   - encoding: the family of Eve's conditional states over the Fourier oracle and Definition 3.4 → the published eveState over the uniform law on bit functions fb (f = (−1)^{fb}), and smoothHMin; reason: Remark 3.5: for finitely many oracles a normalized family is a classical-quantum state
--   - encoding: log, ln → Real.logb 2, Real.log; reason: §3.1: logarithms are to base 2 unless written ln
--   - encoding: N = 2^n, N^{1/3}, N^{−1/3}, √N → (2 : ℝ)^n with Real.rpow and Real.sqrt; reason: Lean convention; same values
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 7.2, p. 59 (PDF p. 62); Definition 3.4, p. 18 (PDF p. 21)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Squaring
import Definitions.Def_TightQLB_Supplement_Entropy
open QAlgorithms MeasureTheory

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 7.2 (Certified randomness from Fourier sampling)**, p.59 (PDF p.62).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let `q ≥ 1` and `δ ≥ 0`, and consider an experiment in the Fourier ensemble in which the device
makes at most `q` queries and has score `B(A) ≥ 3 − 2/N − δ`. Let `η₀` and `λ̄_q` be given by
`η₀ = λ̄_q + (δ/(2(1 − 1/N)) + λ̄_q/(1 − 1/N) + λ̄_q²)^{1/2}`, `λ̄_q = (2/√N) Σ_{t=0}^{q−1} √t`. (64)
If `η₀ < 1`, then for every `η ∈ [η₀, 1]`,
`H^η_min(Z | RE)_ρ ≥ n − 4 log q − log(n + 2) − 3 − 2 log(1/(1 − η₀))`. (65) Moreover, `λ̄₁ = 0`, and
`η₀ ≤ √δ + 2 q^{3/4}N^{−1/4} + 3 q^{3/2}N^{−1/2}`. (66)"

**Formalization Note.**
* The experiment is the published `TightQLB.Experiment` (Definition 3.1 in channel form) with the
  value oracle; its score is the published `Experiment.score`.
* `ρ` is the experiment's family `f ↦ (ρ^f_z)_z = (A.eveState (O_f) z)_z` over the uniform law of
  the oracle (`fourierOracleLaw`); Eve's knowledge of `ω` (the register `R`) enters through the
  measurement chosen per oracle in `p_guess`. `H^η_min` is `smoothHMin` (Definition 3.4).
* `log` is `Real.logb 2` (§3.1); `λ̄` is written as the function `q ↦ (2/√N) Σ_{t<q} √t`; `n ≥ 1`. -/
theorem theorem_7_2 {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) (δ : ℝ) (hδ : 0 ≤ δ) {W E : Type}
    [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
    (A : Experiment n q (Qubits n × Bool) W E)
    (hscore : 3 - 2 / (2 : ℝ) ^ n - δ ≤ A.score) :
    let lamBar : ℕ → ℝ := fun k =>
      2 / Real.sqrt ((2 : ℝ) ^ n) * ∑ t ∈ Finset.range k, Real.sqrt (t : ℝ)
    let η₀ : ℝ := lamBar q + Real.sqrt (δ / (2 * (1 - 1 / (2 : ℝ) ^ n)) +
      lamBar q / (1 - 1 / (2 : ℝ) ^ n) + lamBar q ^ 2)
    (η₀ < 1 → ∀ η : ℝ, η₀ ≤ η → η ≤ 1 →
      (n : ℝ) - 4 * Real.logb 2 q - Real.logb 2 ((n : ℝ) + 2) - 3 -
          2 * Real.logb 2 (1 / (1 - η₀)) ≤
        smoothHMin (fourierOracleLaw n) η (fun fb z => A.eveState (valueOracle fb) z)) ∧
    lamBar 1 = 0 ∧
    η₀ ≤ Real.sqrt δ + 2 * (q : ℝ) ^ (3 / 4 : ℝ) * ((2 : ℝ) ^ n) ^ (-(1 / 4 : ℝ)) +
      3 * (q : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by sorry

end TightQLB.Supplement
