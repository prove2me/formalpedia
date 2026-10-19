-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P41_jc_nonnegative_bound
-- name    : QAlgorithms.Papers.Independent.Information100.P41.jc_nonnegative_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:29:59.94556+00:00
-- url     : https://prove2.me/theorems/42ad0077-06d6-42e6-8e4e-1b5320b13c79
-- title:
--   Nonnegative ground-input JC KD weights and coherence bound
-- statement:
--   Use the resonant ground-atom single-rail JC experiment with $0<\bar n<1$, $0\le\eta\le1$, and $\sin\theta\ne0$. The field state has diagonal $(1-\bar n,\bar n)$ and real off-diagonal $\eta\sqrt{\bar n(1-\bar n)}$. Its atomic output $R$ is the partial trace of the exact isometry $|0\rangle\mapsto|g,0\rangle$, $|1\rangle\mapsto\cos\theta|g,1\rangle-i\sin\theta|e,0\rangle$. For every orthonormal output spectral resolution $R=\sum_m\lambda_mP_m$, let $\Pi_x$ denote energy-basis projectors. The actual ground-input KD weights reduce to $Q(n,x,m,y)=\mathbf1_{n=x=g}\operatorname{Tr}(\Pi_yP_mR)$. They and the coherence change obey
--
--   $$Q(n,x,m,y)\in\mathbb R_{\ge0},\qquad \Delta C=C(R)-C(|g\rangle\langle g|)\le\ln(1+A_C),$$
--
--   where $C(X)=S(DX)-S(X)$ uses natural logarithms and $A_C=\operatorname{Tr}((DR)^{-1}(R-DR)R)$. This is a concrete JC specialization, including possibly singular output states.
-- source:
--   Anomaly fluctuation theorem for quantum coherence dynamics, arXiv:2609.06632v1, PDF p. 4, Ground-input KD specialization

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Information100.P41

/-- PDF p.4: real nonnegative ground-input KD weights and the coherence bound.
Every orthonormal final spectral resolution is allowed, including zero eigenvalues. -/
theorem jc_nonnegative_bound (eta nbar theta : ℝ)
    (heta : 0 ≤ eta ∧ eta ≤ 1) (hnbar : 0 < nbar ∧ nbar < 1)
    (htheta : Real.sin theta ≠ 0) :
    (∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) (p : Fin 2 → ℝ),
      jcOutput eta nbar theta = (U : Matrix (Fin 2) (Fin 2) ℂ) *
        Matrix.diagonal (fun j => (p j : ℂ)) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ →
      ∀ n x nOut xOut : Fin 2,
        0 ≤ (jcKD eta nbar theta U n x nOut xOut).re ∧
        (jcKD eta nbar theta U n x nOut xOut).im = 0) ∧
    jcChange eta nbar theta ≤ Real.log (1 + (jcAnomaly eta nbar theta).re) := by sorry

end QAlgorithms.Papers.Independent.Information100.P41

end
