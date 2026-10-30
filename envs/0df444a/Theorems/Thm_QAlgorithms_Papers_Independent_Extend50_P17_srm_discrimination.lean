-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_srm_discrimination
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.srm_discrimination
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:51:44.423497+00:00
-- url     : https://prove2.me/theorems/8c921362-e9c4-49e3-9a17-d733a2716c56
-- title:
--   Unnumbered generalized state-discrimination bound / Eq.(29)
-- statement:
--   Let $d,k\ge1$ and $2k\le N$. Use the normalized signals $\sigma_i$, their sum $\rho$, and the completed square-root measurement $\Pi_i$. Write $M=k!\binom Nk$ for the number of ordered outcomes, $\bar\rho=\rho/\operatorname{Tr}\rho$, and $p_{\rm dist}=M^{-1}\sum_i\operatorname{Tr}(\Pi_i\sigma_i)$. Then
--
--   $$r:=\frac1M\sum_i\operatorname{rank}(\sigma_i)=d^{N-k},\qquad p_{\rm dist}\ge\frac1{Mr\operatorname{Tr}(\bar\rho^2)},\qquad F=\frac M{d^{2k}}p_{\rm dist}.$$
--
--   Here $F$ is entanglement fidelity for the fixed resource. The factor $M$ follows Eq. (29); its omission in Eq. (7) is a source error. This statement applies to the specified SRM, with kernel completion contributing zero signal overlap.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 9, Unnumbered generalized state-discrimination bound / Eq.(29)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF pp.4,9, Eqs.(5),(29): corrected discrimination inequality with M outcomes.
The missing M in printed Eq.(7) is restored from Eq.(29). -/
theorem srm_discrimination (d N k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hNk : 2 * k ≤ N) :
    (outcomeCount N k : ℝ)⁻¹ * (∑ a : MPBTPortSelection N k,
      (Matrix.rank (mpbtSignal d N k a) : ℝ)) = (d : ℝ)^(N-k) ∧
    1 / ((outcomeCount N k : ℝ) * (d : ℝ)^(N-k) *
      ((normalizedSum d N k)^2).trace.re) ≤ discrimination d N k ∧
    mpbtFidelity d N k = (outcomeCount N k : ℝ) / (d : ℝ)^(2*k) *
      discrimination d N k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
