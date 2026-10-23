-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_normalizedSelectivity
-- name    : QAlgorithms.Papers.Independent.Information100.P37.normalizedSelectivity
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-19T11:08:13.509372+00:00
-- url     : https://prove2.me/theorems/7a9c6fa6-97a1-424f-a911-3eece450a81a
-- title:
--   §V.B–D, Eq. (42): normalized selectivity and Hadamard scaling
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Assume $d\ge2$ and $C_U>0$. Let $\gamma_d=2d/\sqrt{(d-1)(d+2)(d+3)}$, $A=G-\operatorname{Tr}G\,H_d/(d-1)$, and $\Xi_U^2=(2\|A\|_F^2+6\|\operatorname{diag}A\|_2^2)/D_d$. Then
--   $$S_B(U)=\frac{\Delta_U}{\gamma_d C_U}=\sqrt{1+\frac{\Xi_U^2}{\gamma_d^2C_U^2}}\ge1,\qquad S_B(U)=1\ \Longleftrightarrow\ A=0.$$
--   For flat transition probabilities, $\Delta_U/C_U=\gamma_d$. The dimension factor obeys the ratio limit
--   $$\lim_{d\to\infty}\frac{\gamma_d}{2/\sqrt d}=1.$$
--   The limit is taken through natural dimensions.
--
--   Normalized selectivity measures excess fluctuations, and the limit gives the relative-deviation scaling of Hadamard generators.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 6, §V.B–D, Eq. (42): normalized selectivity and Hadamard scaling

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.6, (42),(46): normalized selectivity and ratio-limit Hadamard scaling. -/
theorem normalizedSelectivity (hd : 2 ≤ Fintype.card ι) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hC : 0 < cgp (conjSuperop U)) :
    selectivity (conjSuperop U) = Real.sqrt (1 + excess (response U) ^ 2 /
      (gammaFactor (Fintype.card ι) ^ 2 * cgp (conjSuperop U) ^ 2)) ∧
    1 ≤ selectivity (conjSuperop U) ∧
    (selectivity (conjSuperop U) = 1 ↔ anisotropy (response U) = 0) ∧
    (IsFlat U → cgpd (conjSuperop U) / cgp (conjSuperop U) = gammaFactor (Fintype.card ι)) ∧
    Tendsto (fun d : ℕ => gammaFactor d / (2 / Real.sqrt (d : ℝ))) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
