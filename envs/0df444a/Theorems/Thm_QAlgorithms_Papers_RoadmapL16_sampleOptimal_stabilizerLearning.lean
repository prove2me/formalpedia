-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL16_sampleOptimal_stabilizerLearning
-- name    : QAlgorithms.Papers.RoadmapL16.sampleOptimal_stabilizerLearning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:45:36.086848+00:00
-- url     : https://prove2.me/theorems/a2b595e4-7fdd-46ea-a931-3552cdfa785e
-- title:
--   Sample-optimal learning of stabilizer states
-- statement:
--   Let $n\ge 1$ be the number of qubits and let $0<\delta<1/8$ be the allowed failure probability. An unknown normalized pure stabilizer state $|\psi\rangle$ is provided as identical copies. Let $L_\delta(n)$ be the least number of copies with which one quantum procedure can identify every such state with probability at least $1-\delta$. The minimum permits arbitrary collective measurements, ancillas, internal randomness and adaptivity. Identification means outputting a valid tableau of $n$ independent signed Pauli generators whose common $+1$ eigenspace is the input state; global phase and the choice of generators are irrelevant. Then
--
--   $$
--   n+\left\lceil\log_2\frac1\delta\right\rceil-3
--   \le L_\delta(n)\le
--   n+\left\lceil\log_2\frac1\delta\right\rceil+4.
--   $$
--
--   Furthermore, for every such $n$ and $\delta$, there is a quantum learner receiving at most $n+\lceil\log_2(1/\delta)\rceil+4$ copies and retaining them through adaptive operations, which identifies every input stabilizer state with failure probability at most $\delta$. There are absolute constants $C>0$ and $s_0\ge1$, independent of $n$, $\delta$ and the input state, such that this learner has computational time
--
--   $$
--   \operatorname{time}\le Cn\bigl(n+\ln(1/\delta)\bigr)^4
--   \qquad\text{whenever }n+\ln(1/\delta)\ge s_0.
--   $$
--
--   Time counts elementary quantum gates, measurements, fair coins and Boolean operations, including classical and reversible arithmetic, finite-precision rotation synthesis and tableau reconstruction. The sample and success bounds have no asymptotic threshold. This determines the leading sample coefficient to be one and attains the bound with an efficient learner.
--
--   **Formalization Note** The minimum is represented in $\mathbb N\cup\{\infty\}$, with an empty feasible set assigned $\infty$; the upper bound implies finiteness. The lower inequality is written as $n+\lceil\log_2(1/\delta)\rceil\le L_\delta(n)+3$ to avoid natural subtraction. The theorem's printed statement leaves the qubit domain implicit; $n\ge1$ follows the lower-bound proof on PDF p.7, since the zero-qubit state requires zero copies.
-- source:
--   Sample-optimal learning of stabilizer states, arXiv:2609.10974v1, Theorem 1, PDF p. 2. https://arxiv.org/abs/2609.10974v1 . PDF SHA-256: 2834b0d5fa118d59e3ac593a357959d7bd97300bd10419b72b2fb971b24232b9.

import Definitions.Def_QAlgorithms_Defs_RetainedStabilizerLearners
set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapL16

open QAlgorithms.Stabilizer QAlgorithms.StabilizerLearning

/-- Chang, Caro, Larocca and West, *Sample-optimal learning of stabilizer states*,
arXiv:2609.10974v1, Theorem 1, PDF p.2; operational and time accounting on pp.3,5,12-13,21-22.
The implicit qubit domain is `n >= 1`, as used by the lower-bound proof on p.7:
at `n = 0` the unique physical state needs no copies, so the printed lower bound fails.
`copyComplexity` is the unrestricted, worst-case POVM minimum in the extended naturals.
Writing the lower bound with `+ 3` avoids truncated natural subtraction. The efficient witness
retains its input registers through adaptive trials; its time counts elementary Clifford+T
gates, measurements, coins, Boolean operations, storage initialization and tableau decoding.
Success means a valid signed stabilizer tableau specifying the input density matrix, so it
does not depend on a vector's global phase or a particular choice of generators.
The sample bounds and worst-case success hold throughout the domain; only the uniform
asymptotic runtime bound has a threshold. Natural logarithms are used only in runtime,
and base two is retained in the exact sample ceiling. -/
theorem sampleOptimal_stabilizerLearning :
    ∃ C : ℝ, 0 < C ∧ ∃ threshold : ℝ, 1 ≤ threshold ∧
      ∀ (n : ℕ) (delta : ℝ), 1 ≤ n → 0 < delta → delta < 1 / 8 →
        let c : ℕ := ⌈Real.logb 2 delta⁻¹⌉₊
        ((n + c : ℕ) : ℕ∞) ≤ copyComplexity n delta + 3 ∧
        copyComplexity n delta ≤ ((n + c + 4 : ℕ) : ℕ∞) ∧
        ∃ L : RetainedCopyLearner n,
          L.copies ≤ n + c + 4 ∧
          (∀ psi : EuclideanSpace ℂ (Qubits n), ∀ hpsi : IsStabilizerState psi,
            (open Classical in
              ∑ result : Fin (n * (2 * n + 2)) → Bool,
                if IsValidTableau (decodeTableau n (List.ofFn result)) ∧
                    tableauProjector (decodeTableau n (List.ofFn result)) = pureDensity psi
                then retainedLearnerLaw L psi hpsi.1 result else 0) ≥ 1 - delta) ∧
          (threshold ≤ (n : ℝ) + Real.log delta⁻¹ →
            (L.time : ℝ) ≤ C * (n : ℝ) * ((n : ℝ) + Real.log delta⁻¹) ^ 4) := by sorry

end QAlgorithms.Papers.RoadmapL16
