-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P76_retainedSeedDecoupling
-- name    : QAlgorithms.Papers.Independent.Information100.P76.retainedSeedDecoupling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:05:21.269987+00:00
-- url     : https://prove2.me/theorems/192bbf94-7a5a-41a9-9fbe-8ca4b1b3a806
-- title:
--   Lemma A.3: second moment and joint decoupling with a retained physical seed
-- statement:
--   Let $C=M\otimes G$ have positive finite dimensions $D_C=mg$, $m=\dim M$, and let $H$ be any positive finite reference space. Suppose $\rho_{CH}$ is a normalized density matrix satisfying $\operatorname{rank}\rho_H\le K$ and $\|\rho_{CH}\|_\infty\le\lambda$. For a nonempty finite uniform exact unitary two-design $(V_z)$ on $C$, put $\rho_{MH}^{(z)}=\operatorname{Tr}_G[(V_z\otimes I_H)\rho_{CH}(V_z^*\otimes I_H)]$. Then
--
--   $$\mathbb E_z\left\|\rho_{MH}^{(z)}-\pi_M\otimes\rho_H\right\|_1\le\sqrt{\frac{m^2K\lambda}{D_C}}.$$
--
--   If the actual independent uniform classical seed $Z$ is retained, its controlled output satisfies
--
--   $$D(\rho_{ZMH},\pi_Z\otimes\pi_M\otimes\rho_H)\le\frac12\sqrt{\frac{m^2K\lambda}{D_C}}.$$
--
--   The seed starts in product with $CH$ jointly. The norm in the expectation is trace norm, the cap is operator norm, and $D$ is half trace distance. The definition of exact two-design uses its full two-copy Haar moment, with dimension one treated without division by zero. This is a joint decoupling guarantee for a retained random label, not the selection of one label for every user.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, PDF p. 20, Lemma A.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open Filter

/-- PDF p.20, Lemma A.3: trace-norm decoupling from a uniform exact two-design,
including the factor one half when the independent actual seed is retained. -/
theorem retainedSeedDecoupling {m g h J : ℕ}
    (hm : 0 < m) (hg : 0 < g) (hh : 0 < h) (hJ : 0 < J)
    (rho : Matrix ((Fin m × Fin g) × Fin h) ((Fin m × Fin g) × Fin h) ℂ)
    (hrho : IsDensityMatrix rho) (K : ℕ) (lambda : ℝ)
    (hrank : Matrix.rank (traceLeft rho) ≤ K) (hcap : ‖rho‖ ≤ lambda)
    (V : Fin J → Matrix.unitaryGroup (Fin m × Fin g) ℂ)
    (hdesign : isExactTwoDesign V) :
    (1 / (J : ℝ)) * (∑ j, traceNorm (decoupledOutput rho (V j) -
      Matrix.kronecker (maximallyMixed m) (traceLeft rho))) ≤
        Real.sqrt ((m : ℝ) ^ 2 * K * lambda / (m * g)) ∧
    halfDistance (retainedSeedOutput rho V)
      (Matrix.kronecker (maximallyMixed J)
        (Matrix.kronecker (maximallyMixed m) (traceLeft rho))) ≤
      Real.sqrt ((m : ℝ) ^ 2 * K * lambda / (m * g)) / 2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P76

end
