-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_generalQuadraticMoment
-- name    : QAlgorithms.Papers.Independent.Information100.P37.generalQuadraticMoment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:21:20.518512+00:00
-- url     : https://prove2.me/theorems/52031693-8e91-45bc-b97d-192c25b3110f
-- title:
--   Appendix B, Eq. (B1) and Table I: general quadratic second moment
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let $G$ now be any real symmetric $d\times d$ matrix with $G\mathbf1=0$, without a positivity assumption. Then
--   $$\mathbb E_{\nu_d}(p^TGp)^2=\frac{(\operatorname{Tr}G)^2+2\operatorname{Tr}(G^2)+6\sum_iG_{ii}^2}{D_d}.$$
--   The expectation uses the same full-simplex Dirichlet law.
--
--   The contraction applies to arbitrary symmetric zero-row-sum forms, beyond physical responses.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 13, Appendix B, Eq. (B1) and Table I: general quadratic second moment

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.13, Appendix B, (B1), Table I: generic symmetric zero-row-sum contraction. -/
theorem generalQuadraticMoment [Nonempty ι] (G : Matrix ι ι ℝ)
    (hs : G.IsSymm) (hz : G.mulVec (fun _ => 1) = 0) :
    (∫ p, (quadratic G p) ^ 2 ∂simplexLaw ι) =
      (G.trace ^ 2 + 2 * (G * G).trace + 6 * diagonalSq G) / fourthDenominator (Fintype.card ι) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
