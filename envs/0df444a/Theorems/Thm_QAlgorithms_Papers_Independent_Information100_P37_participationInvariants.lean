-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_participationInvariants
-- name    : QAlgorithms.Papers.Independent.Information100.P37.participationInvariants
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:04:35.765087+00:00
-- url     : https://prove2.me/theorems/b3b83f77-9856-4951-b1c1-1e88d60404d2
-- title:
--   §III.C, Eqs. (18)–(19): participation invariants
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Set $s_j=\sum_iP_{ij}^2$, $S=\sum_js_j$, and $R=\|P^TP\|_F^2$. Then
--   $$\operatorname{Tr}G=d-S,\qquad \operatorname{Tr}(G^2)=d-2S+R,\qquad \sum_jG_{jj}^2=\sum_j(1-s_j)^2.$$
--   Here the Frobenius square is the sum of squares of real matrix entries.
--
--   The additional invariants distinguish column correlations and inhomogeneity beyond the mean.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 4, §III.C, Eqs. (18)–(19): participation invariants

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.4, (18)--(19): all three participation invariant identities. -/
theorem participationInvariants [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (response U).trace = (Fintype.card ι : ℝ) - totalParticipation U ∧
    (response U * response U).trace = (Fintype.card ι : ℝ) - 2 * totalParticipation U + realFrobeniusSq ((transition U)ᵀ * transition U) ∧
    diagonalSq (response U) = ∑ j, (1 - columnParticipation U j) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
