-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_projection_criterion
-- name    : QAlgorithms.Papers.Independent.Information100.P50.projection_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:06:58.339237+00:00
-- url     : https://prove2.me/theorems/ede67cb0-09a7-4a53-b04b-433a32df3ad4
-- title:
--   Unnumbered §5.2 ARN projection criterion: If a mean satisfies f_sigma(0+)=f_sigma'(infinity)=0, for any CP pair with fixed independent Kraus W and deriv
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For a fixed linearly independent Kraus family $(V_k)_{k=1}^r$, put $\Omega(X)=\sum_k V_kXV_k^*$, $W=[\operatorname{vec}(V_1)\ \cdots\ \operatorname{vec}(V_r)]$, and $\Psi_T(X)=\sum_{k,l}T_{kl}V_kXV_l^*$. An effect $T$ determines the pair $(\Psi_T,\Psi_{I-T})$ with common sum $\Omega$. This parametrizes exactly the source's pairs and derivatives, by the ARN correspondence. All derivatives compared use this same family.
--
--   A Kubo–Ando mean $\sigma$ has a nonnegative operator-monotone representing function $f_\sigma$ with $f_\sigma(1)=1$. Set $g_\sigma(t)=t f_\sigma((1-t)/t)$ for $0<t<1$, $g_\sigma(0)=f_\sigma'(\infty)$, and $g_\sigma(1)=f_\sigma(0+)$. Matrix functions use spectral functional calculus and singular means use decreasing positive regularization.
--
--   Suppose both endpoint quantities of the representing function vanish. For an ARN effect $T$,
--
--   $$J(\Psi_T)\sigma J(\Psi_{I-T})=0\iff\operatorname{spec}(T)\subseteq\{0,1\}\iff T^2=T.$$
--
--   The effect is already Hermitian, so idempotence means an orthogonal projection. The statement includes the empty-rank case. It concerns the Choi mean, not the scalar geometric fidelity, whose minimum eigenvalue can vanish even when the mean is nonzero.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 19, Unnumbered §5.2 ARN projection criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Unnumbered Section 5.2 ARN projection criterion, source PDF p.19.
It concerns the zero Choi mean, not vanishing of a scalar minimum eigenvalue. -/
theorem projection_criterion {dx dy r : ℕ}
    (s : Mean) (hs0 : atZero s.f = 0) (hsinf : atInfinity s.f = 0)
    (V : Fin r → Matrix (Fin dy) (Fin dx) ℂ) (hV : LinearIndependent ℂ V)
    (T : M r) (hT : IsEffect T) :
    (connectionOp s.toConnection (choiMatrix (arnFamily V T)) (choiMatrix (arnFamily V (1 - T))) = 0 ↔
      spectrum ℝ T ⊆ ({0, 1} : Set ℝ)) ∧
    (connectionOp s.toConnection (choiMatrix (arnFamily V T)) (choiMatrix (arnFamily V (1 - T))) = 0 ↔
      T * T = T) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
