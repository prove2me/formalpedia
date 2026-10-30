-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_equal_dimension_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.equal_dimension_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:38:43.664308+00:00
-- url     : https://prove2.me/theorems/246dfd76-711a-4ae7-b968-3e6257fbfd30
-- title:
--   Unnumbered equal logical/local dimension corollary of Theorem18
-- statement:
--   Let an isometry $V:L\to\bigotimes_{i=1}^n A_i$ encode a logical system of dimension $d\ge1$ into $n\ge1$ finite subsystems of positive dimensions $d_i$. A located erasure replaces erased sites by fixed pure states and supplies an orthogonal location flag. Write $\epsilon_{\rm worst}=\sqrt{1-f_{\rm worst}^2}$, where one CPTP recovery is optimized before minimizing root entanglement fidelity over all unit vectors on $L\otimes R$, with $R\simeq L$. Write $\epsilon_e=\sqrt{1-f_e^2}$ for optimal root entanglement fidelity at the normalized maximally entangled input. Unless specified otherwise, single-site erasure is uniform. Assume $d\ge2$, continuous transversal covariance for the full defining logical $SU(d)$ action, and $\max_i d_i=d$. Then $$\epsilon_{\rm worst}\ge\frac1{2n}.$$ Equality of every local dimension to $d$ is sufficient; the exact binomial bound only needs the maximum dimension.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 57, Unnumbered equal logical/local dimension corollary of Theorem18

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF p.57, highlighted equal-dimension corollary of Theorem 18. -/
theorem equal_dimension_bound {d n : ℕ} (c : CovariantErasureCodeData d n) (hd : 2 ≤ d)
    (hc : SUCovariant c) (hlocal : c.maxDim = d) :
    (2 * (n : ℝ))⁻¹ ≤ errorWorst c.uniformNoise := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
