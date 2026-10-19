-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_finiteSampleMean
-- name    : QAlgorithms.Papers.Independent.Information100.P37.finiteSampleMean
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:14:11.091756+00:00
-- url     : https://prove2.me/theorems/867fa4f0-82df-425c-b6f4-cf25d025d386
-- title:
--   §VI.B, Eqs. (62)–(64): finite-sample mean
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let $N\ge1$ independent populations $p_1,\ldots,p_N$ each have law $\nu_d$, and suppose each generated coherence is observed exactly. For $\widetilde C_N=N^{-1}\sum_{j=1}^NX_U(p_j)$,
--   $$\mathbb E\widetilde C_N=C_U,\qquad \operatorname{Var}(\widetilde C_N)=\frac{\Delta_U^2}{N}.$$
--   For every $\epsilon>0$,
--   $$\sqrt{\mathbb E(\widetilde C_N-C_U)^2}\le\epsilon\quad\Longleftrightarrow\quad N\ge\frac{\Delta_U^2}{\epsilon^2}.$$
--   The sampling is represented by the canonical finite product of $N$ copies of $\nu_d$.
--
--   CGPD determines the statistical input-sampling cost of mean estimation; no finite-shot quantum measurement noise is modeled.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 8, §VI.B, Eqs. (62)–(64): finite-sample mean

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.8, (62)--(64): unbiased mean, variance and exact RMS sample condition. -/
theorem finiteSampleMean [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (N : ℕ) (hN : 1 ≤ N) :
    let E := conjSuperop U
    (∫ p, empiricalMean E p ∂sampleLaw ι N) = cgp E ∧
    (∫ p, (empiricalMean E p - cgp E) ^ 2 ∂sampleLaw ι N) = cgpd E ^ 2 / (N : ℝ) ∧
    (∀ e : ℝ, 0 < e →
      (Real.sqrt (∫ p, (empiricalMean E p - cgp E) ^ 2 ∂sampleLaw ι N) ≤ e ↔
        cgpd E ^ 2 / e ^ 2 ≤ (N : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
