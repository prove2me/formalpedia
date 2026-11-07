-- Prove2me | Theorems.Thm_StationarityTest_lemma_2_23
-- name    : StationarityTest.lemma_2_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:43.385955+00:00
-- url     : https://prove2.me/theorems/8a91db47-a0d7-4976-ab1b-1f26dde4aa04
-- title:
--   Lemma 2.23 — Pauli shadows after disjoint channels: $2^{O(w)}O(\eta^{-2}\log(ms/\delta))$ copies
-- statement:
--   There are a constant $C>0$ and an exponent $K$ such that the following holds. Let $m,s\ge1$, $\eta>0$, $\delta\in(0,1)$, and let $P_1,\dots,P_m$ be distinct $w$-local Pauli observables on $n$ qubits. Let $A_1,\dots,A_s\subseteq[n]$ be pairwise disjoint, and let $\Phi_1,\dots,\Phi_s$ be channels, where $\Phi_j$ is given by a circuit $c_j$ over $\{H,T,\mathrm{CNOT}\}$ acting only on the qubits of $A_j$ and $a_j$ ancillas, followed by tracing out the ancillas. There is a learner, fixed before the state, that uses at most
--
--   $$N=C\cdot2^{Cw}\cdot\eta^{-2}\cdot\big(1+\log(ms/\delta)\big)$$
--
--   copies and time at most $C\big(n\,m\,N\,(1+\sum_j(|c_j|+a_j))\big)^K$. For every $n$-qubit state $\sigma$, with probability at least $1-\delta$ it returns estimates of $\operatorname{tr}[\Phi_j[\sigma]P_i]$ within $\eta$ for every $i\in[m]$ and $j\in[s]$.
--
--   A coloring argument reduces this to Theorem 2.22. It is the tool by which Algorithm 4 measures all the short-time evolved baseline tests in parallel.
--
--   Differences from the source:
--   - reading: "efficient CPTP maps Φ_j" acting only on A_j; time "poly(n, m, N_samp)" → Φ_j given by a circuit c_j over {H, T, CNOT} on A_j and a_j ancillas, then tracing out the ancillas; time ≤ C(n·m·N·(1 + Σ_j(|c_j| + a_j)))^K; reason: a learner can only apply maps it can implement, and an efficient map's implementation cost is polynomial; charging it rules out unbounded maps at zero cost
--   - generalization: "partition the n qubits into disjoint subsets A_1, …, A_s" → pairwise disjoint subsets, not necessarily covering [n]; reason: a partition is an instance
--   - reading: "Fix η, δ > 0" (inherited) and "2^{O(w)} · O(η^{−2} log(m·s/δ))" → δ ∈ (0, 1) and C · 2^{Cw} · η^{−2} · (1 + log(ms/δ)); reason: as in Theorem 2.22
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma 2.23, (51), p.19

import Definitions.Def_StationarityTest_Learner

open Matrix

namespace StationarityTest

/-- **Lemma 2.23 (Pauli shadows after disjoint channels)**, p.19 (Bergamaschi, *The
stationarity test*, arXiv:2610.01074, held file sha256 0b7e46fb…). In the context of
Theorem 2.22, partition the `n` qubits into disjoint subsets `A_1, …, A_s ⊆ [n]` and let
`Φ_1, …, Φ_s` be efficient CPTP maps, `Φ_j` acting only on `A_j`. There is a learning algorithm
using `N_samp := 2^{O(w)} · O(η^{−2} log(m·s/δ))` (51) copies of `σ` which, with probability
`≥ 1 − δ`, returns estimates of `tr[Φ_j[σ] P_i]` to additive error `η` for every `i ∈ [m]`,
`j ∈ [s]`, in `poly(n, m, N_samp)` classical and quantum time.

**Formalization Note.** "Efficient CPTP map acting only on `A_j`" is read as: `Φ_j` is given by
a circuit `c_j` over `{H, T, CNOT}` on the `n` qubits and `a_j` ancillas in `|0⟩`, whose gates
touch only qubits of `A_j` and ancillas, followed by tracing out the ancillas
(`circuitChannel`); the time bound counts the size of these circuits,
`≤ C (n · m · N · (1 + Σ_j (|c_j| + a_j)))^K`. The `A_j` need only be pairwise disjoint (not
cover `[n]`). Copies `≤ C · 2^{Cw} · η^{−2} (1 + log(m s/δ))`, with `δ ∈ (0, 1)` and
`O(log x)` read as `O(1 + log x)` as in Theorem 2.22. Estimates are indexed by `(i, j)` through
`finProdFinEquiv`. -/
theorem lemma_2_23 : ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n w m s : ℕ, 1 ≤ m → 1 ≤ s →
    ∀ η δ : ℝ, 0 < η → 0 < δ → δ < 1 →
    ∀ P : Fin m → KLocal n 1 w, Function.Injective P →
    ∀ A : Fin s → Finset (Fin (n * 1)), (∀ j j', j ≠ j' → Disjoint (A j) (A j')) →
    ∀ (a : Fin s → ℕ) (c : (j : Fin s) → QAlgorithms.Circuit QAlgorithms.htcxGateSet (n * 1 + a j)),
    (∀ j, ActsOnlyOn (c j) (A j)) →
    ∃ len wp : ℕ, ∃ L : GibbsLearner (n * 1) ((m * s) * (len + 1)),
      (L.copiesUsed : ℝ) ≤ C * 2 ^ (C * w) * (η⁻¹) ^ 2 * (1 + Real.log (m * s / δ)) ∧
      (L.time : ℝ) ≤ C * ((n : ℝ) * m * (C * 2 ^ (C * w) * (η⁻¹) ^ 2 * (1 + Real.log (m * s / δ))) *
          (1 + ∑ j, (((c j).length : ℝ) + a j))) ^ K ∧
      ∀ σ : Op n 1, QAlgorithms.IsDensityMatrix σ →
        1 - δ ≤ L.successProb σ (fun x => ∀ (i : Fin m) (j : Fin s),
          |decodeBlocks finProdFinEquiv len wp x (i, j) -
            (trace (circuitChannel (c j) σ * (P i).1.mat)).re| ≤ η) := by sorry

end StationarityTest
