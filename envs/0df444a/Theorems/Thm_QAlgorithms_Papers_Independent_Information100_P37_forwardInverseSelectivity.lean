-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_forwardInverseSelectivity
-- name    : QAlgorithms.Papers.Independent.Information100.P37.forwardInverseSelectivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:05:55.071678+00:00
-- url     : https://prove2.me/theorems/a021f106-7774-43d5-bfea-ee4b2aaac146
-- title:
--   §IV.C, Eqs. (30)–(33): forward–inverse selectivity
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Put $s_j=\sum_iP_{ij}^2$ and $r_i=\sum_jP_{ij}^2$. Then
--   $$C_U=C_{U^\dagger},\qquad \Delta_U^2-\Delta_{U^\dagger}^2=\frac6{D_d}\left[\sum_j(1-s_j)^2-\sum_i(1-r_i)^2\right].$$
--   For the explicit real unitary
--   $$U_0=\frac12\begin{pmatrix}1&-1&0&\sqrt2\\1&1&\sqrt2&0\\-1&-1&\sqrt2&0\\-1&1&0&\sqrt2\end{pmatrix},$$
--   $C_{U_0}=C_{U_0^\dagger}=1/8$, $\Delta_{U_0}^2=59/6720$, and $\Delta_{U_0^\dagger}^2=1/120$.
--
--   The computed witness shows that inversion can change selectivity while preserving average strength.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 4, §IV.C, Eqs. (30)–(33): forward–inverse selectivity

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF pp.4--5, (30)--(33): forward--inverse identity and the explicit witness. -/
theorem forwardInverseSelectivity [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    cgp (conjSuperop U) = cgp (conjSuperop Uᴴ) ∧
    cgpd (conjSuperop U) ^ 2 - cgpd (conjSuperop Uᴴ) ^ 2 =
      6 / fourthDenominator (Fintype.card ι) *
        ((∑ j, (1 - columnParticipation U j) ^ 2) -
         ∑ i, (1 - rowParticipation U i) ^ 2) ∧
    inverseWitness ∈ Matrix.unitaryGroup (Fin 4) ℂ ∧
    cgp (conjSuperop inverseWitness) = 1 / 8 ∧
    cgp (conjSuperop inverseWitnessᴴ) = 1 / 8 ∧
    cgpd (conjSuperop inverseWitness) ^ 2 = 59 / 6720 ∧
    cgpd (conjSuperop inverseWitnessᴴ) ^ 2 = 1 / 120 := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
