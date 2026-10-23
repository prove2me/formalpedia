-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_unitaryFaithfulness
-- name    : QAlgorithms.Papers.Independent.Information100.P37.unitaryFaithfulness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:09:34.51671+00:00
-- url     : https://prove2.me/theorems/3711b10f-4233-442a-8d6a-dac0dca8b800
-- title:
--   Corollary 9, Faithfulness for unitaries
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   In every dimension $d\ge1$,
--   $$\Delta_U=0\ \Longleftrightarrow\ C_U=0\ \Longleftrightarrow\ U\text{ is monomial in }B.$$
--   Monomiality permits both arbitrary unit-modulus column phases and a permutation of basis vectors.
--
--   Both statistics are faithful to the absence of coherence generation by a unitary.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 6, Corollary 9, Faithfulness for unitaries

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.6, Corollary 9: both zero criteria, also valid in dimension one. -/
theorem unitaryFaithfulness [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (cgpd (conjSuperop U) = 0 ↔ cgp (conjSuperop U) = 0) ∧
    (cgp (conjSuperop U) = 0 ↔ IsIncoherent U) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
