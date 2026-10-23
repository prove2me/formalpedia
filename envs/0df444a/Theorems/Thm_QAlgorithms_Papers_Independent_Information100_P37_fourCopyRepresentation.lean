-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_fourCopyRepresentation
-- name    : QAlgorithms.Papers.Independent.Information100.P37.fourCopyRepresentation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:15:46.487791+00:00
-- url     : https://prove2.me/theorems/54a93783-4a91-4dfb-beb1-74937e2593bd
-- title:
--   Proposition 15, Four-copy representation
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let $S$ swap two ordered copies, let $D_B$ dephase one copy, and put $K_B=S-D_B^{\otimes2}(S)$. For every density matrix $\sigma$,
--   $$c_B(\sigma)=\operatorname{Tr}[K_B\sigma^{\otimes2}].$$
--   With $\Omega_B^{(4)}=\mathbb E\rho_p^{\otimes4}$,
--   $$M_2(U)=\operatorname{Tr}[(K_B\otimes K_B)U^{\otimes4}\Omega_B^{(4)}U^{\dagger\otimes4}].$$
--   The first factor $K_B$ acts on copies $(1,2)$ and the second on $(3,4)$. The traces are real; the scalar representation takes their real parts.
--
--   The exact observable identity gives a four-copy representation without asserting an unsupplied measurement cost.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 8, Proposition 15, Four-copy representation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF pp.8--9, Proposition 15 and (71): exact two- and four-copy observables. -/
theorem fourCopyRepresentation (d : ℕ) (hd : 1 ≤ d) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    (∀ s : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix s →
      coherence s = ((coherenceObservable (Fin d) * Matrix.kronecker s s).trace).re) ∧
    moment (conjSuperop U) 2 =
      ((fourCopyObservable d * piKron 4 U * momentState d 4 * (piKron 4 U)ᴴ).trace).re := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
