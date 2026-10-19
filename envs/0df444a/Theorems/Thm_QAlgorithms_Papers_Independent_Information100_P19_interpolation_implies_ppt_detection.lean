-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_interpolation_implies_ppt_detection
-- name    : QAlgorithms.Papers.Independent.Information100.P19.interpolation_implies_ppt_detection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:03:29.315395+00:00
-- url     : https://prove2.me/theorems/9da00563-a1a3-4ef0-8b14-d6d5483586ce
-- title:
--   Theorem 6.4
-- statement:
--   For every normalized bipartite PSD state $\rho$,
--   $$q_3\ge r_1^2\implies r_2\ge r_1^3,$$
--   so strict standard interpolation detection implies strict three-moment PPT detection. The inclusion is strict: at $p=3/10$ the qutrit isotropic state $p|\Phi_3\rangle\langle\Phi_3|+(1-p)I_9/9$ has
--   $$q_3-r_1^2=-16/5625<0,\qquad r_2-r_1^3=140461/22781250>0.$$
--   Thus the witness is detected only by the PPT test among this pair.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 41, Theorem 6.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Theorem 6.4; arXiv:2609.29471v1, PDF pp.41, 42. -/
theorem interpolation_implies_ppt_detection  :
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef → mass X=1 →
      (rMoment X 1^2 ≤ powerTrace (transposeB X) 3 → rMoment X 1^3 ≤ rMoment X 2) ∧
      (rMoment X 2 < rMoment X 1^3 → powerTrace (transposeB X) 3 < rMoment X 1^2)) ∧
    (isotropic3 (3/10)).PosSemidef ∧ mass (isotropic3 (3/10))=1 ∧
    powerTrace (transposeB (isotropic3 (3/10))) 3-rMoment (isotropic3 (3/10)) 1^2 = -16/5625 ∧
    rMoment (isotropic3 (3/10)) 2-rMoment (isotropic3 (3/10)) 1^3 = 140461/22781250 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
