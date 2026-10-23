-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_qubitLaw
-- name    : QAlgorithms.Papers.Independent.Information100.P37.qubitLaw
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:11:43.117492+00:00
-- url     : https://prove2.me/theorems/990d58e3-8c30-4a4e-a740-899cc1fb3647
-- title:
--   §V.E, Eq. (50) and Appendix F: full qubit law
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let $d=2$ and $X_{\max}=3C_U$. If $C_U>0$, the law of $X_U$ has Lebesgue density
--   $$f_U(x)=\begin{cases}\dfrac1{2\sqrt{X_{\max}x}},&0<x<X_{\max},\\0,&\text{otherwise}.\end{cases}$$
--   If $C_U=0$, its law is the point mass $\delta_0$. Values assigned to the density at the endpoints do not change the measure.
--
--   This gives the entire qubit profile and handles its degenerate branch without dividing by zero.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 7, §V.E, Eq. (50) and Appendix F: full qubit law

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF pp.7,15, (50),(F1): qubit density and the degenerate point-mass branch. -/
theorem qubitLaw (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    let E := conjSuperop U
    let xmax := 3 * cgp E
    (0 < cgp E → coherenceLaw E = volume.withDensity (fun x : ℝ =>
      ENNReal.ofReal (if 0 < x ∧ x < xmax then 1 / (2 * Real.sqrt (xmax * x)) else 0))) ∧
    (cgp E = 0 → coherenceLaw E = Measure.dirac 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
