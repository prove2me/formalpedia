-- Prove2me | Theorems.Thm_QAlgorithms_Childs_compressed_oracle_success_bound
-- name    : QAlgorithms.Childs.compressed_oracle_success_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:34:27.656947+00:00
-- url     : https://prove2.me/theorems/863af0e9-f74c-44c4-a684-826cb81244de
-- title:
--   Standard vs compressed oracle: √p ≤ √p′ + √(k/2^m)
-- statement:
--   Let $n,m,k\ge 0$, let $\Sigma=\{0,1\}^m$ and let $f:[n]\to\Sigma$ be a uniformly random function, accessed by the standard query $O_f:|x\rangle|z\rangle\mapsto|x\rangle|z\oplus f(x)\rangle$. Consider any $t$-query quantum algorithm with a finite workspace $W$: it starts in a fixed unit vector $|s\rangle$ and applies $U_t\,O_f\,U_{t-1}\cdots O_f\,U_0$, where the unitaries $U_0,\dots,U_t$ do not depend on $f$. It then measures its registers $|x,z,w\rangle$ in the computational basis and converts the outcome, by a fixed map, into $k$ input–output pairs $(x_1,z_1),\dots,(x_k,z_k)\in[n]\times\Sigma$. Let $R\subseteq[n]\times\Sigma$.
--
--   Let $p$ be the probability, over the uniform choice of $f$ and the measurement, that $f(x_i)=z_i$ and $(x_i,z_i)\in R$ for every $i\in[k]$.
--
--   Now run the same algorithm with the compressed oracle $(I\otimes I\otimes C^{\otimes n})\Lambda(I\otimes I\otimes C^{\otimes n})$ in place of each query. Here the oracle register $y\in(\Sigma\cup\{\perp\})^n$ starts in $|\perp\rangle^{\otimes n}$, $\Lambda|x\rangle|z\rangle|y\rangle=|x\rangle|z\oplus y_x\rangle|y\rangle$ (the identity when $y_x=\perp$), and $C$ swaps $|\perp\rangle$ with $|\hat 0\rangle=2^{-m/2}\sum_{y\in\Sigma}|y\rangle$ and fixes every $|\hat y\rangle=H^{\otimes m}|y\rangle$ with $y\neq0$. Measure all registers, the oracle register included, in the computational basis. Let $p'$ be the probability that $(x_i,z_i)\in R$ and the oracle register $x_i$ holds $y_{x_i}=z_i$ for every $i\in[k]$. Then
--
--   $$
--   \sqrt{p}\;\le\;\sqrt{p'}+\sqrt{\frac{k}{2^m}} .
--   $$
--
--   The lemma turns probabilities that are easy to compute in the compressed-oracle picture into bounds on the true success probability of an algorithm against a random oracle. Chapter 26 uses it for its lower bounds for unstructured search and collision finding.
--
--   **Formalization Note** The algorithm is a `QueryAlg` with input-independent unitaries and a unit start vector. The output map `out` is an arbitrary function of the measured basis state of the algorithm's registers. $p$ is `randomOracleSuccess` (the average over all $2^{mn}$ functions $f$) and $p'$ is `compressedSuccess`. The pairs $x_i$ may repeat.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 134, Lemma 26.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_CompressedOracle
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- Childs, Lemma 26.1 (PDF p. 134; conclusion as in the proof's (26.15), p. 135).
Let `A` be any `t`-query algorithm with workspace `W` (start state a unit vector, unitaries
fixed independently of the oracle), whose final computational-basis measurement of its own
registers is turned into `k` input–output pairs `(x_1, z_1), …, (x_k, z_k)` by `out`, and let
`R ⊆ [n] × Σ`. Let `p` be the probability, over a uniformly random `f` and the measurement,
that `f(x_i) = z_i` and `(x_i, z_i) ∈ R` for all `i` (`randomOracleSuccess`). Let `p'` be the
probability that, running `A` with the compressed oracle and measuring all registers including
the oracle register, `(x_i, z_i) ∈ R` and the oracle register `x_i` holds `y_{x_i} = z_i` for all
`i` (`compressedSuccess`). Then `√p ≤ √p' + √(k / 2^m)`. -/
theorem compressed_oracle_success_bound {n m k : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    {t : ℕ} (A : QueryAlg (Fin n) (Qubits m) W t)
    (out : (Fin n × Qubits m) × W → (Fin k → Fin n × Qubits m))
    (R : Finset (Fin n × Qubits m)) :
    Real.sqrt (randomOracleSuccess A out R) ≤
      Real.sqrt (compressedSuccess A out R) + Real.sqrt ((k : ℝ) / 2 ^ m) := by
  sorry


end QAlgorithms.Childs
