-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P37_pptKey_nonzeroVolume_larger
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P37.pptKey_nonzeroVolume_larger
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:25:17.035989+00:00
-- url     : https://prove2.me/theorems/1e188a23-9f56-46bb-979f-15c70cef8666
-- title:
--   Unnumbered extension of Observation 3 to larger local dimensions
-- statement:
--   Let $m,n\ge4$ be the two local Hilbert-space dimensions. Embed the physical Hadamard resource $\rho_H$ into the first four basis labels at each party, with zero elsewhere, and denote it by $\widehat\rho_H$. There exist $q\in(0,1)$ and $\varepsilon>0$ such that every Hermitian trace-one matrix $\sigma$ with
--
--   $$\left\|\sigma-\left(q\widehat\rho_H+(1-q)I_{mn}/(mn)\right)\right\|_2<\varepsilon$$
--
--   is a density matrix, is PPT, and has strictly positive distillable key. Thus these states contain a full-dimensional affine ball and have nonzero volume in every such bipartite dimension. Both dimensions must be at least four; a bound on total dimension alone is not asserted.
-- source:
--   Low dimensional bound entanglement with one-way distillable cryptographic key, arXiv:quant-ph/0506203v1, PDF p. 3, Unnumbered extension of Observation 3 to larger local dimensions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P37

noncomputable section

open scoped Matrix BigOperators ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P24
  (Key IsPrivate xForm twist twistingMatrix associatedCCQ transposeSecond transposeBob partyCut)

/-- PDF p.3, sentence following Observation 3: the same full-dimensional ball
statement for all local dimensions m,n>=4, after local embedding and white noise. -/
theorem pptKey_nonzeroVolume_larger (m n : ℕ) (hm : 4 ≤ m) (hn : 4 ≤ n) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ eps : ℝ, 0 < eps ∧
      ∀ sigma : Op (Fin m × Fin n), sigma.IsHermitian → sigma.trace = 1 →
        squaredDistance sigma (noisyEmbeddedHadamard m n q) < eps^2 →
        IsPPTWithKey sigma := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P37

end
