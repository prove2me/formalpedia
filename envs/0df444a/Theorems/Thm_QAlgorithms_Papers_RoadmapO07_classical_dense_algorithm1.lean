-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapO07_classical_dense_algorithm1
-- name    : QAlgorithms.Papers.RoadmapO07.classical_dense_algorithm1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:29:50.692976+00:00
-- url     : https://prove2.me/theorems/358a5f39-7ea9-49a5-91cb-847f0f97bf51
-- title:
--   Algorithm 1: classical dense-entry implementation for ε-optimal zero-sum strategies
-- statement:
--   Let \(n,m\) be positive integers and let \(A\in[-1,1]^{n\times m}\) be the payoff matrix of a zero-sum game. Alice maximizes the payoff and Bob minimizes it. Let \(\Delta_n,\Delta_m\) denote the probability simplexes and let
--   $$
--   v^*=\min_{y\in\Delta_m}\max_{i\in[n]}(Ay)_i.
--   $$
--   For \(0<\varepsilon<1\) and \(0<\delta<1/3\), run the fixed-accuracy branch of Algorithm 1 for
--   $$
--   T=\left\lceil\frac{16}{\varepsilon^2}\ln\!\left(\frac{nm}{\delta}\right)\right\rceil
--   $$
--   completed updates. Starting with zero accumulators \(x,y\), each update independently draws \(a\in[m]\) with probabilities proportional to \(\exp(-A^\mathsf{T}x)\) and \(b\in[n]\) with probabilities proportional to \(\exp(Ay)\), then adds \((\varepsilon/4)e_a\) to \(y\) and \((\varepsilon/4)e_b\) to \(x\). The final accumulators are normalized to give \(\widehat x,\widehat y\).
--
--   There is a classical randomized implementation, chosen independently of the entries of \(A\), whose output distribution is exactly the distribution of these normalized updates. Every update makes exactly \(n+m\) entry queries and uses \(O(n+m)\) numerical work; initialization and final normalization also use \(O(n+m)\) work and make no entry queries. The constants and dimension threshold in these work bounds are universal. In particular, the implementation makes exactly \(T(n+m)\) entry queries and satisfies the joint guarantee
--   $$
--   \Pr\!\left[
--   \widehat x\in\Delta_n,\ \widehat y\in\Delta_m,\quad
--   A\widehat y\le(v^*+\varepsilon)\mathbf 1,\quad
--   A^\mathsf{T}\widehat x\ge(v^*-\varepsilon)\mathbf 1
--   \right]\ge1-\delta.
--   $$
--   This result supplies the classical dense-entry implementation and equilibrium guarantee for Algorithm 1.
--
--   **Formalization Note** Numerical work uses the ideal arithmetic and finite-distribution sampling model of the proof: exponential evaluation, array operations and linear sampling passes are charged explicitly. This is not a finite-bit running-time claim. The integer iteration count is taken from the fixed-accuracy clause of Lemma 1, which Lemma 3 invokes. Updates are indexed by their number of completed steps, resolving Algorithm 1's initialization/indexing discrepancy.
-- source:
--   Quantum algorithms for zero-sum games, arXiv:1904.03180v1, Lemma 3, PDF p. 6. https://arxiv.org/abs/1904.03180v1 . PDF SHA-256: 074f65525b5758f32df5b6afe34774e296bf976d2169b34346eafbc06ecd8732.

import Definitions.Def_QAlgorithms_Defs_ZeroSumDynamics
import Definitions.Def_QAlgorithms_Papers_RoadmapO07_Model
set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapO07

open QAlgorithms.ZeroSum


/-- Lemma 3 of van Apeldoorn and Gilyen, *Quantum algorithms for zero-sum games*,
arXiv:1904.03180v1, PDF p.6: the classical dense-entry implementation of Algorithm 1.
The fixed-accuracy branch uses the ceiling specified in Lemma 1 (PDF p.3) and counts
completed updates from the zero accumulators. Work is ideal numerical work, including
linear cumulative-distribution sampling, as in the proof on p.6; no bit-runtime claim
is made. The concrete program is fixed before the payoff matrix, and both optimality
conditions use the value of the game defined on PDF p.2. -/
theorem classical_dense_algorithm1 :
    ∃ C : ℝ, 0 < C ∧ ∃ size0 : ℕ, 1 ≤ size0 ∧
      ∀ (n m : ℕ) [NeZero n] [NeZero m] (A : Game n m)
        (eps delta : ℝ), 0 < eps → eps < 1 → 0 < delta → delta < 1 / 3 →
      let T : ℕ := ⌈16 * Real.log ((n : ℝ) * m / delta) / eps ^ 2⌉₊
      let initial : EntryState n m := ⟨0, [], 0, false⟩
      let program := denseImplementation n m eps T
      let law := entryProgramLaw A.payoff program initial
      let parts := denseLoopParts program
      let readout : EntryState n m → Option ((Fin n → ℝ) × (Fin m → ℝ)) :=
        fun s => if s.failed then none
          else some (fun i => s.memory i.val, fun j => s.memory (n + j.val))
      let prefixLaw := fun t : ℕ =>
        (entryProgramLaw A.payoff parts.1 initial).bind
          (entryProgramLaw A.payoff (.loop t parts.2.1 .done))
      law.map readout = fixedAccuracyRun A.payoff eps T ∧
      (∀ s ∈ (entryProgramLaw A.payoff parts.1 initial).support,
        s.failed = false ∧ s.trace = [] ∧
          (size0 ≤ n + m → (s.work : ℝ) ≤ C * (n + m))) ∧
      (∀ t < T, ∀ s ∈ (prefixLaw t).support,
        ∀ s' ∈ (entryProgramLaw A.payoff parts.2.1 s).support,
          s'.failed = false ∧ s'.trace.length = s.trace.length + (n + m) ∧
            (size0 ≤ n + m → (s'.work : ℝ) ≤ s.work + C * (n + m))) ∧
      (∀ s ∈ (prefixLaw T).support,
        ∀ s' ∈ (entryProgramLaw A.payoff parts.2.2 s).support,
          s'.failed = false ∧ s'.trace = s.trace ∧
            (size0 ≤ n + m → (s'.work : ℝ) ≤ s.work + C * (n + m))) ∧
      (∀ s ∈ law.support, s.failed = false ∧ s.trace.length = T * (n + m)) ∧
      (law.toOuterMeasure {s | ∃ x y, readout s = some (x, y) ∧
        IsEpsOptimalPair A eps x y}).toReal ≥ 1 - delta := by sorry

end QAlgorithms.Papers.RoadmapO07
