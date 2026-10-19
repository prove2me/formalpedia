-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_allowedRegion
-- name    : QAlgorithms.Papers.Independent.Information100.P37.allowedRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:08:56.048666+00:00
-- url     : https://prove2.me/theorems/2a4d2e91-7229-45e3-b3ae-4575fc523009
-- title:
--   Proposition 8, Allowed CGP–CGPD region
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   For $d\ge2$, with $\gamma_d=2d/\sqrt{(d-1)(d+2)(d+3)}$,
--   $$\gamma_d C_U\le\Delta_U\le\sqrt{C_U\left(\frac{d-1}{d}-C_U\right)}.$$
--   The supporting range is $0\le X_U(p)\le(d-1)/d$ for every simplex population, hence $0\le C_U\le(d-1)/d$.
--
--   These are necessary bounds on the allowed mean–deviation region, without a claim that every point is achievable.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 6, Proposition 8, Allowed CGP–CGPD region

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.6, Proposition 8: both allowed-region inequalities and the supporting range. -/
theorem allowedRegion (hd : 2 ≤ Fintype.card ι) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    let d := (Fintype.card ι : ℝ)
    gammaFactor (Fintype.card ι) * cgp (conjSuperop U) ≤ cgpd (conjSuperop U) ∧
    cgpd (conjSuperop U) ≤ Real.sqrt (cgp (conjSuperop U) * ((d - 1) / d - cgp (conjSuperop U))) ∧
    (∀ p, IsPopulation p → 0 ≤ generated (conjSuperop U) p ∧ generated (conjSuperop U) p ≤ (d - 1) / d) ∧
    0 ≤ cgp (conjSuperop U) ∧ cgp (conjSuperop U) ≤ (d - 1) / d := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
