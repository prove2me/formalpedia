-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_symmetries
-- name    : QAlgorithms.Papers.Independent.Information100.P37.symmetries
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:06:41.607651+00:00
-- url     : https://prove2.me/theorems/9727e7bb-7e84-42b0-a193-23e0f6cac6a2
-- title:
--   Proposition 4, Symmetries
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let $W_L,W_R$ be monomial unitaries: each permutes basis vectors and attaches phases of modulus one. For any unitary $V$ and transformed basis $\widetilde B=\{V|i\rangle\}$,
--   $$\operatorname{Law}(X_{B,U})=\operatorname{Law}(X_{B,W_LU})=\operatorname{Law}(X_{B,UW_R}),$$
--   $$C_{\widetilde B}(U)=C_B(V^\dagger UV),\qquad \Delta C_{\widetilde B}(U)=\Delta C_B(V^\dagger UV).$$
--
--   The full coherence-generation profile respects incoherent relabelings and changes covariantly with the reference basis.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 5, Proposition 4, Symmetries

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.5, Proposition 4: full-law symmetries and covariance under basis change. -/
theorem symmetries [Nonempty ι] (U L R V : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hL : L ∈ Matrix.unitaryGroup ι ℂ)
    (hR : R ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (hLi : IsIncoherent L) (hRi : IsIncoherent R) :
    coherenceLaw (conjSuperop U) = coherenceLaw (conjSuperop (L * U)) ∧
    coherenceLaw (conjSuperop U) = coherenceLaw (conjSuperop (U * R)) ∧
    cgpInBasis V U = cgp (conjSuperop (Vᴴ * U * V)) ∧
    cgpdInBasis V U = cgpd (conjSuperop (Vᴴ * U * V)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
