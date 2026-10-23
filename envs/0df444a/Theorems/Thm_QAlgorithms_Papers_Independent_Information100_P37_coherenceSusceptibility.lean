-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_coherenceSusceptibility
-- name    : QAlgorithms.Papers.Independent.Information100.P37.coherenceSusceptibility
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:15:20.223814+00:00
-- url     : https://prove2.me/theorems/dc44eacd-b89e-4173-9ec7-77965608954a
-- title:
--   Proposition 14, Coherence-generation susceptibility
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   For every real bias parameter $a$, define the normalized tilted probability law by $d\nu_{d,a}=e^{aX_U}d\nu_d/Z_U(a)$, where $Z_U(a)=\mathbb E_{\nu_d}e^{aX_U}$, and let $C_{U,a}=\mathbb E_{\nu_{d,a}}X_U$. Then
--   $$C_{U,0}=C_U,\qquad \left.\frac{dC_{U,a}}{da}\right|_{a=0}=\Delta_U^2.$$
--   The derivative is taken for the mean under the normalized law.
--
--   Variance is the linear susceptibility of average coherence to an input-ensemble bias.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 8, Proposition 14, Coherence-generation susceptibility

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.8, Proposition 14: response of the normalized tilted mean. -/
theorem coherenceSusceptibility [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    tiltedMean (conjSuperop U) 0 = cgp (conjSuperop U) ∧
    HasDerivAt (tiltedMean (conjSuperop U)) (cgpd (conjSuperop U) ^ 2) 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
