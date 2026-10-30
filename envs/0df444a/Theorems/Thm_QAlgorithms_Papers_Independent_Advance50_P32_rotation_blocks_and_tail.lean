-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P32_rotation_blocks_and_tail
-- name    : QAlgorithms.Papers.Independent.Advance50.P32.rotation_blocks_and_tail
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:26:54.363349+00:00
-- url     : https://prove2.me/theorems/43c17cfb-40df-4a2a-b7b5-a822573b5ee8
-- title:
--   Section 5.2, Eq. (27): total-number block diagonalization and positive tail
-- statement:
--   Fix $s>0$, a measurable nonnegative displacement density $q$ of integral one, and a rotationally covariant channel $N$. Let $A=\int q(\xi)N(W_\xi\rho_sW_\xi^*)\otimes W_\xi\rho_sW_\xi^*\,d\xi$, and let $E$ be its common uniform rotation by $U_\theta\otimes U_\theta$. Define $Q_j$ as the projector onto total photon number $j$ and $P_c=\sum_{j=0}^cQ_j$. Then $E$ is a density operator and
--
--   $$E=\sum_{j=0}^{\infty}Q_jAQ_j,\qquad E-P_cEP_c=\sum_{j=c+1}^{\infty}Q_jEQ_j\ge0,\qquad\|E-P_cEP_c\|_1\longrightarrow0.$$
--
--   Thus the displayed block expansions converge in trace norm, not merely entrywise. For every rectangular cutoff $R_c$, imposing $\Omega=\sum_{j=0}^{2c}Q_j\Omega Q_j$ on the positive PPT finite SDP with $\operatorname{Tr}_B\Omega\le I$ leaves its optimum unchanged. The same phase rotates both tensor factors, and $q$ need not itself be isotropic. These properties supply the positive-tail certificate used by the finite bound.
-- source:
--   Squeezing the limit: Quantum benchmarks for the teleportation and storage of squeezed states, arXiv:0808.2260v1, PDF p. 12, Section 5.2, Eq. (27); SDP symmetry p.13

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology TensorProduct

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State IsTraceClassChannel BreaksTraceClassEntanglement
   productCoeff traceSize rotationMeasure)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P35 (tracePair)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Next46.P13 (coordinateBasis)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel vacuum realFockTracePair)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section 5.2, pp.12–13, (27): common-rotation block decomposition, positive tail,
trace-norm convergence, and the lossless finite SDP symmetry used on p.13. -/
theorem rotation_blocks_and_tail (s : ℝ) (hs : 0 < s) (q : ℝ × ℝ → ℝ)
    (hq : DisplacementDensity q)
    (N : FockOperatorArray (NumberLabel 1) → FockOperatorArray (NumberLabel 1))
    (hN : RotationCovariantNoise N) :
    let E := ensembleOperator s q N
    IsDensity E ∧
    (∀ i j, E i j = ∑' c, numberBlock c (unrotatedEnsemble s q N) i j) ∧
    (∀ c, PositiveKernel (E - triangularCut c E) ∧
      (∀ i j, (E - triangularCut c E) i j =
        ∑' k : ℕ, numberBlock (c + 1 + k) E i j)) ∧
    Tendsto (fun c => traceSize (E - triangularCut c E)) atTop (nhds 0) ∧
    (∀ c, finitePPTOptimum c E = SymmetricFinitePPTOptimum c E) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P32

end
