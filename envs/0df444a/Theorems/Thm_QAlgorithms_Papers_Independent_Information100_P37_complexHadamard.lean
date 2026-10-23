-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_complexHadamard
-- name    : QAlgorithms.Papers.Independent.Information100.P37.complexHadamard
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-19T11:10:36.229379+00:00
-- url     : https://prove2.me/theorems/7da5e0de-aef6-42e2-8a79-64e908a0617b
-- title:
--   Corollary 10, Complex Hadamard generators
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Assume $d\ge2$ and $|U_{ij}|^2=1/d$ for every $i,j$. With $S_B(U)=\Delta_U/(\gamma_d C_U)$ and $\gamma_d=2d/\sqrt{(d-1)(d+2)(d+3)}$,
--   $$G=H_d,\quad C_U=\frac{d-1}{d(d+1)},\quad
--   \Delta_U=\frac{2\sqrt{d-1}}{(d+1)\sqrt{(d+2)(d+3)}},\quad S_B(U)=1.$$
--   The dimension restriction makes the selectivity denominator strictly positive.
--
--   Complex Hadamard generators lie on the isotropic lower boundary.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 6, Corollary 10, Complex Hadamard generators

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.6, Corollary 10: exact complex Hadamard values; positive-mean dimension. -/
theorem complexHadamard (hd : 2 ≤ Fintype.card ι) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hf : IsFlat U) :
    let d := (Fintype.card ι : ℝ)
    cgp (conjSuperop U) = (d - 1) / (d * (d + 1)) ∧
    cgpd (conjSuperop U) = 2 * Real.sqrt (d - 1) / ((d + 1) * Real.sqrt ((d + 2) * (d + 3))) ∧
    selectivity (conjSuperop U) = 1 ∧ response U = zeroSumProjector ι := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
