-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapO20_approximateMatrixMultiplication_circuit
-- name    : QAlgorithms.Papers.RoadmapO20.approximateMatrixMultiplication_circuit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:41:59.002989+00:00
-- url     : https://prove2.me/theorems/08b2fe2d-2a4e-47f5-ade2-f21b0d2a9ba6
-- title:
--   Approximate products of square real matrices in the classical and quantum circuit models
-- statement:
--   Fix a classical exact-arithmetic matrix multiplication implementation with achievable exponent $\omega\ge 2$. Let $n\ge1$, $K\ge1$, and let $A_1,\ldots,A_K\in\mathbb R^{n\times n}$ be arbitrary matrices. Write $F=\prod_{j=1}^K\|A_j\|_F$, where $\|A\|_F=(\sum_{i,j}A_{ij}^2)^{1/2}$. Given absolute accuracy $\varepsilon>0$ and failure probability $0<\delta<1$, there are fixed input-taking classical and quantum circuit families, with classical preprocessing time $\widetilde O(Kn^2)$, which return classical matrices $C_{\rm cl}$ and $C_{\rm q}$ satisfying
--
--   $$
--   \Pr\!\left[\|C_{\rm cl}-A_1\cdots A_K\|_F\le\varepsilon\right]\ge1-\delta,
--   \qquad
--   \Pr\!\left[\max_{i,j}|(C_{\rm q}-A_1\cdots A_K)_{ij}|\le\varepsilon\right]\ge1-\delta.
--   $$
--
--   Apart from input/output and preprocessing overhead, their running times are respectively
--
--   $$
--   \widetilde O\!\left(n^2\left(\frac{3^K F^2}{\varepsilon^2}\right)^{\omega-2}\right),
--   \qquad
--   \widetilde O\!\left(n^2\frac{3^K F}{\varepsilon}\right).
--   $$
--
--   The soft factors include the confidence logarithms and are uniform over dimensions, factors, matrix entries, accuracy, and confidence; constants may depend on the chosen multiplication implementation. Real numbers are represented exactly, and fixed-position retrieval and arithmetic are charged in both models. The quantum output is an ordinary classical matrix. No efficiently addressable classical or quantum memory is required.
--
--   The case $K=1$ returns the input matrix exactly. For $K>1$ and $F\le\varepsilon$, both families return zero; this includes every zero factor. These branches still pay for the input and classical output. The displayed online scales are clamped below by $n^2$, and the formal total bound includes $Kn^2$ explicitly. This result compares approximate products in two different error norms under the same circuit access model.
--
--   **Formalization Note** Lean uses $k=K-1$ interfaces and computes $F^2$ during charged classical preprocessing. Rounded, confidence-dependent sample budgets select members of circuit families fixed before the matrices. The classical law is computed from one fixed list of exact-real arithmetic, random-coin and comparison instructions, with each comparison writing a 0/1 register value and every instruction charged; quantum probabilities and work are computed from the frozen exact-real mean-estimation circuit language. No approximation guarantee or arbitrary runtime number is assumed as a field of an algorithm.
-- source:
--   Randomized and quantum approximate matrix multiplication, arXiv:2510.08509v1, Theorem 1.3 (continues on p.6); Theorems 4.10–4.11, pp.21–23, PDF p. 5. https://arxiv.org/abs/2510.08509v1 . PDF SHA-256: 7b334b23191f9fcfe8168955347ed4f07b27dfc4de47d07ee9bc5800dba95cfa.

import Definitions.Def_QAlgorithms_Defs_ClassicalMatrixSketchEstimator
import Definitions.Def_QAlgorithms_Defs_ApproximateMatrixMultiplicationContracts
import Definitions.Def_QAlgorithms_Papers_RoadmapO20_Model
set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapO20

open QAlgorithms MatrixApprox













/-- Original Theorem 1.3, arXiv:2510.08509v1, PDF pp.5-6, both square-matrix clauses;
formal counterparts Theorems 4.10-4.11, pp.21-23. Exact real arithmetic is §2.3, p.8.
Here k interfaces means k+1 factors, including the one-factor case k=0.
The classical power applies to the entire sample scale, including 3^(k+1).
The headline quantum factor remains 3^(k+1), rather than replacing it with the
stronger factor in (17). No source correction to Theorem 1.3 is made.
Circuit families and universal resource constants precede all matrices. The
preprocessor computes the squared Frobenius statistic; integer sample counts
are the source's norm-based precision schedule, rounded upwards. Budget zero
returns zero when the norm-product is at most eps. All success and work claims
are conclusions about computed circuit executions, not fields of the witnesses. -/
theorem approximateMatrixMultiplication_circuit
    (multiplication : MultiplicationImplementation) (omega : ℝ)
    (implemented : IsAchievableExponent multiplication omega) :
    ∃ constant : ℝ, 0 < constant ∧ ∃ power : ℕ,
    ∃ preprocessingRegisters : ℕ → ℕ → ℕ,
    ∃ preprocessing : (n k : ℕ) → ExactArithmetic.ClassicalCircuit
      ((k+1)*(n*n)) (preprocessingRegisters n k) 1,
    ∃ classical : (n k width repeats : ℕ) → O20ClassicalCircuit n ((k+1)*(n*n)),
    ∃ quantum : (n k : ℕ) → (eps delta : ℝ) → (budget : ℕ) →
      MeanEstimatorCircuit n ((k+1)*(n*n)),
    ∀ n : ℕ, 0 < n → ∀ k : ℕ,
    o20PreprocessingWork (preprocessing n k) ≤
      constant*(k+1)*n^2*max 1 (Real.log (2+(n : ℝ)+k))^power ∧
    ∀ A : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ,
    (∀ state ∈ (ExactArithmetic.classicalExecution (preprocessing n k) (o20Input A)).support,
      state.failed = false ∧ state.memory ((preprocessing n k).output 0) = o20SquaredF A) ∧
    ∀ eps delta : ℝ, 0 < eps → 0 < delta → delta < 1 →
    let sizes := o20Budgets n k (o20SquaredF A) eps delta
    let classicalCircuit := classical n k sizes.1 sizes.2.2
    let quantumCircuit := quantum n k eps delta sizes.2.1
    let data := o20Input A
    let classicalScale := (n : ℝ)^2 *
      max 1 (((3 : ℝ)^(k+1)*o20F A^2/eps^2)^(omega-2))
    let quantumScale := (n : ℝ)^2 * max 1 ((3 : ℝ)^(k+1)*o20F A/eps)
    let inputSize := ((k+1)*(n*n) : ℕ)
    (∀ result ∈ (o20ClassicalLaw classicalCircuit data).support,
      result.2.1 = false ∧ (result.2.2 : ℝ) ≤
        constant*(inputSize+classicalScale)*o20Logs n k eps delta classicalScale power) ∧
    ((o20ClassicalLaw classicalCircuit data).toOuterMeasure
      {result | frobeniusSuccess A eps result.1}).toReal ≥ 1-delta ∧
    quantumCircuit.Admissible data ∧
    (o20QuantumWork quantumCircuit : ℝ) ≤
      constant*(inputSize+quantumScale)*o20Logs n k eps delta quantumScale power ∧
    (quantumCircuit.executionLaw data
      {result | maxSuccess A eps result.1}).toReal ≥ 1-delta ∧
    (k = 0 →
      (∀ result ∈ (o20ClassicalLaw classicalCircuit data).support, result.1 = A 0) ∧
      quantumCircuit.executionLaw data {result | result.1 = A 0} = 1) ∧
    (0 < k → o20F A ≤ eps →
      (∀ result ∈ (o20ClassicalLaw classicalCircuit data).support, result.1 = 0) ∧
      quantumCircuit.executionLaw data {result | result.1 = 0} = 1 ∧
      (∀ result ∈ (o20ClassicalLaw classicalCircuit data).support,
        (result.2.2 : ℝ) ≤ constant*inputSize*o20Logs n k eps delta 1 power) ∧
      (o20QuantumWork quantumCircuit : ℝ) ≤
        constant*inputSize*o20Logs n k eps delta 1 power) := by sorry

end QAlgorithms.Papers.RoadmapO20
