-- Prove2me | Theorems.Thm_StationarityTest_theorem_2_22
-- name    : StationarityTest.theorem_2_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:42.286329+00:00
-- url     : https://prove2.me/theorems/223ca8f0-4ec3-46d2-88bf-9c4129d04332
-- title:
--   Theorem 2.22 (Pauli shadow tomography, [HKP20]) — $O(4^w\eta^{-2}\log(m/\delta))$ copies estimate $m$ $w$-local Pauli expectations
-- statement:
--   There are a constant $C>0$ and an exponent $K$ such that the following holds. Let $n,w\ge0$, $m\ge1$, $\eta>0$ and $\delta\in(0,1)$, and let $P_1,\dots,P_m\in S^w_{[n]}$ be distinct $w$-local Pauli observables on $n$ qubits. There is a learner, fixed before the state, that uses at most
--
--   $$N=C\cdot4^w\cdot\eta^{-2}\cdot\big(1+\log(m/\delta)\big)$$
--
--   copies and time at most $C(n\,m\,N)^K$. For every $n$-qubit state $\sigma$, with probability at least $1-\delta$ it returns estimates $\hat e_1,\dots,\hat e_m$ with $|\hat e_j-\operatorname{tr}[\sigma P_j]|\le\eta$ for all $j$.
--
--   Classical shadows learn all $m$ local expectation values at once, with a cost logarithmic in $m$. This gives the $\log n$ dependence of the structure learning algorithm.
--
--   **Formalization Note** The learner is the mission's `GibbsLearner` on $n$ qubits (sites with $q=1$), and its estimates are read by the fixed dyadic decoder.
--
--   Differences from the source:
--   - reading: "Fix η, δ > 0" → η > 0 and δ ∈ (0, 1); reason: for δ ≥ 1 the success claim is empty and log(m/δ) can be negative, so the bound would be unsatisfiable; the source's regime is δ < 1
--   - reading: "O(2^{2w} · η^{−2} · log(m/δ))" → C · 4^w · η^{−2} · (1 + log(m/δ)) with C universal; reason: at m = 1 and δ → 1 the printed log(m/δ) tends to 0 while any learner whose output depends on σ uses a copy; 1 + log is the uniform form of the asymptotic bound and equals it up to a constant once m/δ ≥ e
--   - reading: "there exists a learning algorithm", "poly(n, m, N_samp) classical and quantum time" → a GibbsLearner (gates over {H, T, CNOT}, classical control by Boolean circuits, computational-basis measurements), time ≤ C(n·m·N)^K; reason: the paper names no model of computation; this is the published CopyLearner model for mixed states
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Theorem 2.22, (50), p.18

import Definitions.Def_StationarityTest_Learner

open Matrix

namespace StationarityTest

/-- **Theorem 2.22 (Pauli shadow tomography, [HKP20, Theorem 1, Proposition 3])**, p.18
(Bergamaschi, *The stationarity test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Fix
`η, δ > 0`. Let `σ` be an `n`-qubit state and `P_1, …, P_m ∈ S^w_[n]` distinct `w`-local Pauli
observables. There is a learning algorithm using `N_samp := O(2^{2w} η^{−2} log(m/δ))` (50) copies
of `σ` which, with probability `≥ 1 − δ`, returns estimates of `tr[σ P_i]` to additive error `η`
for each `i ∈ [m]`, in `poly(n, m, N_samp)` classical and quantum time.

**Formalization Note.** `n` qubits are `n` sites with `q = 1`. The learner (`GibbsLearner`) is
chosen after `n, w, m, η, δ` and the observables and before `σ`; it outputs `m` dyadic estimates
through the fixed decoder `decodeBlocks`. Constants: `∃ C > 0, K` universal, copies
`≤ C · 4^w · η^{−2} · (1 + log(m/δ))` and time `≤ C (n · m · N)^K` with `N` that bound. Two
readings: `δ ∈ (0, 1)` (for `δ ≥ 1` the claim is empty and `log(m/δ)` can be negative), and
`O(log(m/δ))` as `O(1 + log(m/δ))`: at `m = 1`, `δ → 1` the printed bound tends to `0` while any
learner whose output depends on `σ` uses at least one copy. `tr[σ P_i]` is real for a density
matrix and is written as a real part. -/
theorem theorem_2_22 : ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n w m : ℕ, 1 ≤ m → ∀ η δ : ℝ, 0 < η →
    0 < δ → δ < 1 → ∀ P : Fin m → KLocal n 1 w, Function.Injective P →
    ∃ len wp : ℕ, ∃ L : GibbsLearner (n * 1) (m * (len + 1)),
      (L.copiesUsed : ℝ) ≤ C * 4 ^ w * (η⁻¹) ^ 2 * (1 + Real.log (m / δ)) ∧
      (L.time : ℝ) ≤ C * ((n : ℝ) * m * (C * 4 ^ w * (η⁻¹) ^ 2 * (1 + Real.log (m / δ)))) ^ K ∧
      ∀ σ : Op n 1, QAlgorithms.IsDensityMatrix σ →
        1 - δ ≤ L.successProb σ (fun x => ∀ j : Fin m,
          |decodeBlocks (Equiv.refl (Fin m)) len wp x j - (trace (σ * (P j).1.mat)).re| ≤ η) := by sorry

end StationarityTest
