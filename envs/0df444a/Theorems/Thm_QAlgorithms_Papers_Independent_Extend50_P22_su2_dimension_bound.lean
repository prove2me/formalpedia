-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_su2_dimension_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.su2_dimension_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:30:14.232316+00:00
-- url     : https://prove2.me/theorems/4f1c0d0a-8774-46a7-b550-eccd831e46c3
-- title:
--   Unnumbered qubit SU(2) dimension bound, Eq.(50)
-- statement:
--   Let an isometry $V:L\to\bigotimes_{i=1}^n A_i$ encode a logical system of dimension $d\ge1$ into $n\ge1$ finite subsystems of positive dimensions $d_i$. A located erasure replaces erased sites by fixed pure states and supplies an orthogonal location flag. Write $\epsilon_{\rm worst}=\sqrt{1-f_{\rm worst}^2}$, where one CPTP recovery is optimized before minimizing root entanglement fidelity over all unit vectors on $L\otimes R$, with $R\simeq L$. Write $\epsilon_e=\sqrt{1-f_e^2}$ for optimal root entanglement fidelity at the normalized maximally entangled input. Unless specified otherwise, single-site erasure is uniform. For a logical qubit, assume continuous transversal $SU(2)$ covariance and put $D=\max_i d_i$. Then $$1\le2n(D-1)\epsilon_{\rm worst}.$$ This is the representation-based dimension bound for logical spin one-half; real subtraction retains the contradiction when $D=1$.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 14, Unnumbered qubit SU(2) dimension bound, Eq.(50)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.14, (50), logical spin 1/2. A cross-multiplied real-valued dimension difference. -/
theorem su2_dimension_bound {n : ℕ} (c : CovariantErasureCodeData 2 n) (hc : SUCovariant c) :
    1 ≤ 2 * n * ((c.maxDim : ℝ) - 1) * errorWorst c.uniformNoise := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
