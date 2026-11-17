-- Prove2me | Theorems.Thm_TightQLB_Supplement_theorem_7_9
-- name    : TightQLB.Supplement.theorem_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:27:43.37122+00:00
-- url     : https://prove2.me/theorems/15fdc438-3822-4b44-87df-685be2312dd2
-- title:
--   Theorem 7.9 — certified randomness from Haar-random states: $H^\eta_{\min}(Z\mid RE)\ge n-2\log q-\log H_N-2-\log\frac1{1-\eta_0^2}$
-- statement:
--   Let $N=2^n$ with $n\ge1$, $q\ge1$ and $\delta\ge0$, and consider an experiment with the canonical oracle of a Haar-random state $|\phi\rangle$ (Eve holds a register $E$ and learns $\phi$ afterwards) in which the device makes at most $q$ queries and has expected score $B(\mathcal A)\ge\beta_N-\delta$, $\beta_N=2N/(N+1)$. Put
--
--   $$
--   \eta_0=\big(3(\delta+2\sqrt2\,\Lambda_q+72\,\Lambda_q^2)+\Lambda_q^2\big)^{1/2},\qquad \Lambda_q=\frac{c_0}{\sqrt N}\sum_{t=0}^{q-1}\sqrt{2t+1}\le\sqrt3\,c_0\frac{q^{3/2}}{\sqrt N},
--   $$
--
--   with $c_0=54$. If $\eta_0<1$, then for every $\eta\in[\eta_0,1]$,
--
--   $$
--   H^\eta_{\min}(Z\mid RE)_\rho\ge n-2\log q-\log H_N-2-\log\frac1{1-\eta_0^2},
--   $$
--
--   where $H_N=\sum_{j=1}^N1/j\le\ln N+1$. Moreover $\eta_0\le\sqrt{3\delta}+4\sqrt{c_0}\,q^{3/4}N^{-1/4}+26\,c_0\,q^{3/2}N^{-1/2}$. Logarithms are to base 2.
--
--   The output of a near-ideal Haar sampler with few queries retains all but $2\log q+\log H_N+O(1)$ bits of private randomness.
--
--   **Formalization Note** The experiment is the base mission's channel-form experiment with query register $\mathbb C|\bot\rangle\oplus\mathbb C^N$ and the canonical oracle; $\rho$ is the family of Eve's conditional states over the Haar law. The inequalities $\Lambda_q\le\sqrt3c_0q^{3/2}/\sqrt N$ and $H_N\le\ln N+1$, displayed in the statement, are conclusions.
--
--   Differences from the source:
--   - reading: the operational experiment of Definition 3.1 (record, adaptive operations, at most q queries along every path) → a density matrix on A × E, q + 1 oracle-independent CPTP rounds on A, q controlled queries between them and a POVM, as in the base mission's TightQLB.Experiment; reason: the proof of Lemma 3.2, Steps 1–2, puts every experiment in this form and conversely every such channel form is an experiment of Definition 3.1
--   - encoding: the family of Eve's conditional states over the Haar oracle and Definition 3.4 → the published eveState with the canonical oracle over haarTargetLaw, and smoothHMin; reason: Definition 3.4 is the definition for the continuous register R (Remark 3.5)
--   - encoding: the absolute constant c0 of Theorem 5.21 in Λ_{s,q} → c0 = 54; reason: "The proof gives c0 = 54" (p. 44, PDF p. 47)
--   - encoding: a Haar-random unit vector of C^N → the published haarTargetLaw (the standard Gaussian on C^N normalized); reason: the same law on unit vectors
--   - encoding: log, ln → Real.logb 2, Real.log; reason: §3.1: logarithms are to base 2 unless written ln
--   - encoding: N = 2^n, N^{1/3}, N^{−1/3}, √N → (2 : ℝ)^n with Real.rpow and Real.sqrt; reason: Lean convention; same values
--   - reading: (70) "Moreover, for every q" → stated under the theorem's hypothesis q ≥ 1; reason: "Let q ≥ 1" opens the theorem, and "for every q" says that (70) needs no condition η0 < 1; at q = 0, Λ_0 = 0 and (70) reads √(3δ) ≤ √(3δ)
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), Theorem 7.9, p. 64 (PDF p. 67); Definition 3.4, p. 18 (PDF p. 21)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Haar
import Definitions.Def_TightQLB_Supplement_Entropy
open QAlgorithms MeasureTheory

set_option autoImplicit false

namespace TightQLB.Supplement

/-- **Theorem 7.9 (Certified randomness from Haar-random states)**, p.64 (PDF p.67).

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…).

"Let `q ≥ 1` and `δ ≥ 0`, and consider an experiment with the canonical oracle in which the device
makes at most `q` queries and has score `B(A) ≥ β_N − δ`. Let `η₀` and `Λ_q` be given by
`η₀ = (3(δ + 2√2 Λ_q + 72 Λ_q²) + Λ_q²)^{1/2}`, `Λ_q = (c₀/√N) Σ_{t=0}^{q−1} √(2t + 1) ≤ √3 c₀ q^{3/2}/√N`.
(68) If `η₀ < 1`, then for every `η ∈ [η₀, 1]`,
`H^η_min(Z | RE)_ρ ≥ n − 2 log q − log H_N − 2 − log(1/(1 − η₀²))`, (69) where `H_N ≤ ln N + 1` is the
harmonic number of Lemma 5.24. Moreover, for every `q`,
`η₀ ≤ √(3δ) + 4√c₀ q^{3/4}N^{−1/4} + 26 c₀ q^{3/2}N^{−1/2}`. (70)"

**Formalization Note.**
* The experiment is the published `TightQLB.Experiment` with query register `Option (Qubits n)` and
  the canonical oracle `O_ϕ`; `B(A)` is `haarScore A`. `ρ` is the family
  `ϕ ↦ (A.eveState (O_ϕ) z)_z` over the Haar law; `H^η_min` is `smoothHMin` (Definition 3.4).
* `Λ_q = Λ_{0,q}` is `Lam n 0 q` with `c₀ = 54`; the displayed bound `Λ_q ≤ √3 c₀ q^{3/2}/√N` of (68) and
  `H_N ≤ ln N + 1` are stated as conclusions.
* `log` is `Real.logb 2`, `ln` is `Real.log`; `n ≥ 1`. -/
theorem theorem_7_9 {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) (δ : ℝ) (hδ : 0 ≤ δ) {W E : Type}
    [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
    (A : Experiment n q (Option (Qubits n)) W E) (hscore : betaN n - δ ≤ haarScore A) :
    let η₀ : ℝ := Real.sqrt (3 * (δ + 2 * Real.sqrt 2 * Lam n 0 q + 72 * Lam n 0 q ^ 2) +
      Lam n 0 q ^ 2)
    Lam n 0 q ≤ Real.sqrt 3 * c0 * (q : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt ((2 : ℝ) ^ n) ∧
    harmonicN n ≤ Real.log ((2 : ℝ) ^ n) + 1 ∧
    (η₀ < 1 → ∀ η : ℝ, η₀ ≤ η → η ≤ 1 →
      (n : ℝ) - 2 * Real.logb 2 q - Real.logb 2 (harmonicN n) - 2 -
          Real.logb 2 (1 / (1 - η₀ ^ 2)) ≤
        smoothHMin (haar n) η (fun ϕ z => A.eveState (canonOracle ϕ) z)) ∧
    η₀ ≤ Real.sqrt (3 * δ) + 4 * Real.sqrt c0 * (q : ℝ) ^ (3 / 4 : ℝ) * ((2 : ℝ) ^ n) ^ (-(1 / 4 : ℝ)) +
      26 * c0 * (q : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by sorry

end TightQLB.Supplement
