-- Prove2me | Theorems.Thm_QuarticGap_Supplement_theorem_5_6
-- name    : QuarticGap.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:57:02.052817+00:00
-- url     : https://prove2.me/theorems/e2cd9536-90f7-47e1-8192-fbfc7e686d67
-- title:
--   Theorem 5.6 — Hamiltonian evolution $e^{-iP_W}\psi_0$: $\Omega(n^2/\log n)$ classical, $\widetilde\Theta(\sqrt n)$ quantum queries
-- statement:
--   Fix a rational number $t \in (0,1/64]$, let $P_W = P_W(t)$ be as in (18), and let $\psi_0 = (u,0,u)/\sqrt2$. For every constant $\varepsilon \in (0, t^2/10)$ there are $c > 0$, $C > 0$ and $n_0$ such that, for every power of four $n \ge n_0$:
--
--   1. every classical algorithm with access $\mathrm{SQ}(P_W)$ that samples from $p_{e^{-iP_W}\psi_0}$ within total variation distance $\varepsilon$ for every $W \in \mathcal G$ makes more than $cn^2/\log n$ queries on some $W \in \mathcal G$, and more than $cn^2/\log n$ queries in expectation on some $W\in\mathcal G$;
--   2. a quantum algorithm samples within $\varepsilon$ with at most $C\sqrt n(\log n)^C$ queries;
--   3. every quantum algorithm that samples within $\varepsilon$ for every $W \in \mathcal G$ makes at least $c\sqrt n$ queries.
--
--   The range of errors is of order $t^2$, larger than the $t^4$ of Theorem 5.5 for evolution with the initial vector $b$.
--
--   **Formalization Note** $e^{-iP_W}$ is the matrix exponential; $\psi_0$ is fixed and known classically and prepared by the circuit quantumly. There is no gate clause.
--
--   Differences from the source:
--   - encoding: n a power of four, positions in {0,1}^k → n = 4^ℓ, positions in {0,1}^{2ℓ}, √n = 2^ℓ; reason: the same values of n
--   - reading: a randomized classical algorithm → QueryAlg, a behaviour strategy on transcripts with unrestricted computation; reason: an algorithm with private coins and perfect recall has a behaviour strategy with the same law (Kuhn); the input reaches it only through the answers
--   - encoding: output distribution within total variation distance ε → sampleErr, which counts the mass of non-halting runs as an extra outcome; reason: it is TV for an algorithm that halts almost surely and gives a non-halting algorithm no advantage
--   - encoding: coherent access to the 3n × 3n (or (3n+1) × (3n+1)) matrix → coherent access to the matrix zero padded to 4n × 4n, quantum outputs in the 4n padded coordinates with the target padded by zeros; reason: Remark 4.4 (p.32): the padded rows and columns are zero and known and the targets vanish on them; an output on a padding coordinate only adds error
--   - reading: a fixed binary encoding of the entries → the published ratEnc: sign bit, numerator and denominator in 2ℓ + 2 + size(|num t|·den t) bits; reason: every entry is rational with numerator and denominator of O(log n) bits (§2.4, p.17); the width fits all of them exactly
--   - reading: a quantum algorithm → an oracle circuit on any number of wires, started in |0⟩ and measured at the end, fixed before W and the oracles and correct for every legal choice of the input operations; reason: Definition 2.2: an algorithm must succeed for every choice of the unspecified action; the base goal's convention
--   - reading: quantum query complexity Θ̃(√n) → one circuit over all unitary gates with at most C√n(log n)^C queries, output reading wires, and at least c√n queries for every circuit over all unitary gates with any output map; reason: the proof's Lemma 2.10 gives Ω(√n) and §5 (p.33) says Θ̃(ρ) queries suffice and are necessary; the stronger reading of the lower bound
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Theorem 5.6, p.37

import Mathlib
import Definitions.Def_QuarticGap_Supplement_Pmat

open QAlgorithms

namespace QuarticGap.Supplement

/-- Theorem 5.6 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.37). Fix a rational number
`t ∈ (0, 1/64]`, let `P_W = P_W(t)` be as in (18), and let `ψ₀ = (u, 0, u)/√2`. For every constant
`ε ∈ (0, t²/10)`, there are `c > 0` and `n₀` such that, for every power of four `n ≥ n₀`, every
classical algorithm that samples from `p_{e^{−iP_W}ψ₀}` within total variation distance `ε` for every
`W ∈ G` makes more than `cn²/log n` queries on some `W ∈ G`, and more than `cn²/log n` queries in
expectation on some `W ∈ G`. The quantum query complexity of this task is `Θ̃(√n)`.

**Formalization Note** `n = 4^ℓ`; `e^{−iP_W}` is the matrix exponential. The models are those of the
published goal: classical `QueryAlg` against `SQ(P_W)` on the `3n × 3n` matrix (`ψ₀` is fixed and
known, Definition 2.1); quantum circuits with access to `P_W` zero padded to `4n × 4n` (Remark 4.4),
`ψ₀` being prepared by the circuit itself (Definition 2.2). "Quantum query complexity `Θ̃(√n)`" is
read as: one circuit over all unitary gates, fixed before `W` and the oracles, with at most
`C√n(log n)^C` queries and an output that reads wires, solves the task; and every circuit with any
output map that solves it makes at least `c√n` queries. The theorem has no gate clause. -/
theorem theorem_5_6 (t : ℚ) (ht : 0 < t ∧ t ≤ 1 / 64) (ε : ℝ) (hε : 0 < ε ∧ ε < (t : ℝ) ^ 2 / 10) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ ℓ : ℕ, n₀ ≤ 4 ^ ℓ →
      (∀ alg : QueryAlg (SQQuery (Ix3 ℓ) (Ix3 ℓ)) (SQAns (Ix3 ℓ) (Ix3 ℓ)) (Ix3 ℓ),
        (∀ W ∈ G ℓ, alg.sampleErr (pRespond t W) (lenSqDist (hamVec t W)) ≤ ε) →
        (∃ W ∈ G ℓ, ¬ alg.MakesAtMostReal (pRespond t W)
          (c * ((4 : ℝ) ^ ℓ) ^ 2 / Real.log ((4 : ℝ) ^ ℓ))) ∧
        (∃ W ∈ G ℓ, ENNReal.ofReal (c * ((4 : ℝ) ^ ℓ) ^ 2 / Real.log ((4 : ℝ) ^ ℓ)) <
          alg.expQueries (pRespond t W))) ∧
      (∃ (N : ℕ) (alg : OracleCircuit UnitaryGates (supArity ℓ t) N)
          (w : Fin (2 + 2 * ℓ) ↪ Fin N),
        (totalQueries alg : ℝ) ≤ C * Real.sqrt ((4 : ℝ) ^ ℓ) * Real.log ((4 : ℝ) ^ ℓ) ^ C ∧
        ∀ W ∈ G ℓ, ∀ orc, IsPAccess t W orc →
          tv (qOut alg orc (readWires w)) (lenSqDist (padVec dec3 (hamVec t W))) ≤ ε) ∧
      (∀ (N : ℕ) (alg : OracleCircuit UnitaryGates (supArity ℓ t) N) (out : Qubits N → Idx ℓ),
        (∀ W ∈ G ℓ, ∀ orc, IsPAccess t W orc →
          tv (qOut alg orc out) (lenSqDist (padVec dec3 (hamVec t W))) ≤ ε) →
        c * Real.sqrt ((4 : ℝ) ^ ℓ) ≤ totalQueries alg) := by sorry

end QuarticGap.Supplement
