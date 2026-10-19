-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_firstCumulants
-- name    : QAlgorithms.Papers.Independent.Information100.P37.firstCumulants
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:03:51.034292+00:00
-- url     : https://prove2.me/theorems/0f56fdad-2dbd-4220-bc36-cacf565de025
-- title:
--   §II.C, Eq. (10): first cumulants
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let $Z_U(a)=\mathbb E\exp(aX_U)$ and $K_U(a)=\log Z_U(a)$. Then $Z_U(a)>0$ for every real $a$, and
--   $$K_U'(0)=C_U,\qquad K_U''(0)=\Delta_U^2.$$
--   The derivative identities are conclusions, with no differentiability assumptions added.
--
--   The mean and variance are the first two coherence-generation cumulants.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 3, §II.C, Eq. (10): first cumulants

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.3, (10): first two cumulants; regularity is a conclusion. -/
theorem firstCumulants [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (∀ a : ℝ, 0 < partition (conjSuperop U) a) ∧
    HasDerivAt (cumulant (conjSuperop U)) (cgp (conjSuperop U)) 0 ∧
    HasDerivAt (deriv (cumulant (conjSuperop U))) (cgpd (conjSuperop U) ^ 2) 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
