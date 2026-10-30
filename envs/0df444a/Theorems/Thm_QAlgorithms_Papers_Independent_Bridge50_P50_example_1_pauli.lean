-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_example_1_pauli
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.example_1_pauli
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:41:53.323711+00:00
-- url     : https://prove2.me/theorems/7961c44f-c660-41c3-b610-5e35e023b31e
-- title:
--   Example 1 Pauli: example 1 pauli
-- statement:
--   Let $p_0,p_1,p_2,p_3\ge0$ sum to one and let $W_p(A)=\sum_{k=0}^3p_k\sigma_k A\sigma_k^*$, where $\sigma_0=I$ and $\sigma_1,\sigma_2,\sigma_3$ are the qubit Pauli matrices. Let $S$ be its image on all qubit density matrices. Define
--   $$
--   \lambda=(p_0+p_1-p_2-p_3,\ p_0-p_1+p_2-p_3,\ p_0-p_1-p_2+p_3),\quad q=(1-\max_j|\lambda_j|)/2.
--   $$
--   The set $S$ is invariant under $\rho\mapsto I-\rho$, its divergence center is $I/2$, and every capacity-achieving finite ensemble of minimum support size consists of pairwise commuting positive-weight states. Moreover,
--   $$
--   C(W_p)=\chi(S)=1-h_2(q),\qquad v_{\min}(S)=v_{\max}(S)=q(1-q)\log_2^2\frac{1-q}{q},
--   $$
--   where $h_2$ is binary entropy and the variance is zero at deterministic BSC endpoints. Here $C$ is the unrestricted operational classical capacity, defined using the actual tensor channel and arbitrary joint-state encodings and POVMs.
--
--   Thus the comparison BSC is constructed from the channel itself. The singleton-image completely depolarizing case and noiseless case are included.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 10, Example 1 Pauli

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50

noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelSpace

/-- Example 1, PDF p.10: reflection symmetry, maximally mixed divergence center,
EVERY minimal achieving ensemble commutes, and capacity/dispersion equal those of
the constructed BSC. Includes the singleton image and noiseless endpoints. -/
theorem example_1_pauli (p : Fin 4 → ℝ) (hp : ∀ k, 0 ≤ p k) (htotal : ∑ k, p k = 1) :
    (∀ rho ∈ pauliImage p, (1 : Mat Bool)-rho ∈ pauliImage p) ∧
    divergenceCenter (pauliImage p) = (1/2 : ℝ) • (1 : Mat Bool) ∧
    (∀ E : Ensemble Bool, MinimalAchieving (pauliImage p) E →
      ∀ i j, 0 < E.prob i → 0 < E.prob j → E.state i * E.state j = E.state j * E.state i) ∧
    pauliQuantumCapacity p = 1-QAlgorithms.binEntropy2 (bscCrossover p) ∧
    capacityBits (pauliImage p) = 1-QAlgorithms.binEntropy2 (bscCrossover p) ∧
    vMin (pauliImage p) = bscVariance (bscCrossover p) ∧
    vMax (pauliImage p) = bscVariance (bscCrossover p) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
