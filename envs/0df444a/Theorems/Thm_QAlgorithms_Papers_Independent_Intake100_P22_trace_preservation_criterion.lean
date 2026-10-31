-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_trace_preservation_criterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.trace_preservation_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:45:32.437913+00:00
-- url     : https://prove2.me/theorems/b749f316-14b6-4b42-bbcd-cb9f8620e3fe
-- title:
--   Trace preservation criterion and affine covariance action
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   For a Gaussian map $E$ with given parameters $(A,B,D,C)$, trace preservation on every operator is equivalent to
--   $$
--   E\text{ is trace preserving}\quad\Longleftrightarrow\quad D=0\text{ and }C=1.
--   $$
--   For every regular Gaussian operator with complex covariance $M$, a trace-preserving $E$ has a regular output and
--   $$
--   M'=BMB^T+A.
--   $$
--   Covariances are normalized by the nonzero operator trace. The affine term $A$ is retained. This separates trace preservation from positivity and unitality.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 9, §VI: trace preservation criterion and affine covariance action

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9: TP on every operator iff D=0,C=1; the affine A term remains. -/
theorem trace_preservation_criterion {n : ℕ} (s : CARSystem n)
    (E : Superop (Qubits n) (Qubits n)) (K : GrassmannKernel n) (hE : HasGrassmannKernel s E K) :
    (FullTracePreserving E ↔ K.D = 0 ∧ K.C = 1) ∧
    (FullTracePreserving E → ∀ X M, RegularWith s X M →
      RegularWith s (E X) (K.B * M * K.B.transpose + K.A) ∧
        regularCorrelation s (E X) = K.B * M * K.B.transpose + K.A) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
