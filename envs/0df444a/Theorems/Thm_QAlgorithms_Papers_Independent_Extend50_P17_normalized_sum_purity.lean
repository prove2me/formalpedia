-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_normalized_sum_purity
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.normalized_sum_purity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:51:10.477781+00:00
-- url     : https://prove2.me/theorems/22ede2bf-3564-4f16-81ce-1886068244d2
-- title:
--   Lemma 1 / Eq.(8): purity of the normalized signal sum
-- statement:
--   For integers $d,k\ge1$ and $2k\le N$, let $\sigma_i$ be the trace-one signal operators of Eq. (2), indexed by ordered injections of $k$ ports into $N$ ports. Set $\rho=\sum_i\sigma_i$ and $\bar\rho=\rho/\operatorname{Tr}\rho$. Then
--
--   $$\operatorname{Tr}(\bar\rho^2)=d^{-N-k}\binom Nk^{-1}\binom{d^2+N-1}k.$$
--
--   The trace used for normalization is positive; invertibility of $\rho$ is unnecessary. This evaluates the purity that enters the SRM discrimination bound.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 4, Lemma 1 / Eq.(8): purity of the normalized signal sum

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.4, Lemma 1, Eq.(8), normalized as verified by Eq.(52) on p.11. -/
theorem normalized_sum_purity (d N k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hNk : 2 * k ≤ N) :
    ((normalizedSum d N k)^2).trace =
      (((d : ℂ)^(N + k))⁻¹ * (N.choose k : ℂ)⁻¹ *
        ((d^2 + N - 1).choose k : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
