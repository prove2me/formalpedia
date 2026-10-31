-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_coherent_elimination_of_intermediate_measurements
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P52.coherent_elimination_of_intermediate_measurements
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:49:13.030686+00:00
-- url     : https://prove2.me/theorems/d5be0b0e-f04a-443a-8257-bf347f504b78
-- title:
--   §8: coherent elimination of intermediate measurements
-- statement:
--   Fix a finite adaptive process with $n$ data qubits and $k$ recorded projective measurements. Before measurement $t$, its gate, measured site and orthonormal basis are fixed functions of the preceding $t$ bits; a final unitary may also depend on the full history. Measurement basis vectors are columns of the supplied one-qubit unitary. Let $K_s$ be the chronological gate/projector branch operator for the full history $s\in\{0,1\}^k$. There is a single unitary $V$ on the data and $k$ fresh pointer qubits, selected before the unknown input, such that for every normalized $|\psi\rangle$,
--
--   $$ V(|\psi\rangle\otimes|0^k\rangle)=\sum_s K_s|\psi\rangle\otimes|s\rangle. $$
--
--   Final computational-basis pointer measurement therefore reproduces the entire joint history law $\|K_s\psi\|^2$ and every subnormalized residual density. All finite history-dependent controls are included coherently. No cost bound or normalization on a zero branch is asserted.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, PDF p. 19, §8: coherent elimination of intermediate measurements

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Deferred measurement, PDF p.19: one input-independent unitary on data and
fresh pointer bits reproduces every subnormalized residual state and joint
history law. History-dependent classical controls are included in the coherent
unitary. No efficiency assertion, and no normalization on zero branches. -/
theorem coherent_elimination_of_intermediate_measurements {n k : ℕ} (P : AdaptiveProcess n k) :
    ∃ V : Matrix (Qubits n × Qubits k) (Qubits n × Qubits k) ℂ,
      V ∈ Matrix.unitaryGroup (Qubits n × Qubits k) ℂ ∧
      ∀ (psi : Vec (Qubits n)), IsState psi →
        act V (tensorVec psi (zeroKet k)) = pointerWave P psi ∧
        (∀ s : Qubits k,
          let v : Vec (Qubits n) := WithLp.toLp 2 fun z =>
            act V (tensorVec psi (zeroKet k)) (z,s)
          pureDensity v = pureDensity (act (processBranchOperator P s) psi) ∧
          ‖v‖ ^ 2 = ‖act (processBranchOperator P s) psi‖ ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P52

end
