-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_reliabilityCertificates
-- name    : QAlgorithms.Papers.Independent.Information100.P37.reliabilityCertificates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:13:37.338962+00:00
-- url     : https://prove2.me/theorems/8370f492-4d85-423a-a21b-a0ba059278c0
-- title:
--   §VI.A, Eqs. (58)–(60): reliability certificates
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   For every $\epsilon>0$,
--   $$\Pr_{\nu_d}(X_U\le C_U-\epsilon)\le\frac{\Delta_U^2}{\Delta_U^2+\epsilon^2},\qquad
--   \Pr_{\nu_d}(|X_U-C_U|\ge\epsilon)\le\frac{\Delta_U^2}{\epsilon^2}.$$
--   For $0<\delta<1$, define $L_\delta=\max\{0,C_U-\sqrt{(1-\delta)/\delta}\,\Delta_U\}$. Then
--   $$\Pr_{\nu_d}(X_U\ge L_\delta)\ge1-\delta.$$
--   All probabilities and moments use the same input law $\nu_d$.
--
--   These certificates translate coherence fluctuations into guarantees against low-output inputs.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 7, §VI.A, Eqs. (58)–(60): reliability certificates

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF pp.7--8, (58)--(60): Cantelli, Chebyshev and nonnegative reliability certificate. -/
theorem reliabilityCertificates [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (e : ℝ) (he : 0 < e) :
    let E := conjSuperop U
    (simplexLaw ι).real {p | generated E p ≤ cgp E - e} ≤ cgpd E ^ 2 / (cgpd E ^ 2 + e ^ 2) ∧
    (simplexLaw ι).real {p | |generated E p - cgp E| ≥ e} ≤ cgpd E ^ 2 / e ^ 2 ∧
    (∀ a : ℝ, 0 < a → a < 1 →
      1 - a ≤ (simplexLaw ι).real {p | max 0 (cgp E - Real.sqrt ((1 - a) / a) * cgpd E) ≤ generated E p}) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
