-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_dephasedTensorMoments
-- name    : QAlgorithms.Papers.Independent.Information100.P37.dephasedTensorMoments
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:05:09.614992+00:00
-- url     : https://prove2.me/theorems/44b4be12-b0c5-47b1-bd8f-53dd36e1fcd9
-- title:
--   §IV.A, Eqs. (20)–(22): dephased tensor moments
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   For every integer $n\ge1$, let $\Omega_B^{(n)}=\mathbb E_{\nu_d}\rho_p^{\otimes n}$ and $(d)_n=\prod_{k=0}^{n-1}(d+k)$. If $T_\pi$ permutes the $n$ ordered tensor factors, then
--   $$\Omega_B^{(n)}=D_B^{\otimes n}\left[\frac1{(d)_n}\sum_{\pi\in S_n}T_\pi\right].$$
--   Equivalently, for indices $i_1,\ldots,i_n$,
--   $$\mathbb E\prod_{a=1}^np_{i_a}=\frac1{(d)_n}\sum_{\pi\in S_n}\prod_{a=1}^n\delta_{i_a,i_{\pi(a)}}.$$
--   The moment state is the expectation of a tensor power, rather than a tensor power of an expectation.
--
--   These tensor and scalar identities encode all population moments in one permutation formula.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 4, §IV.A, Eqs. (20)–(22): dephased tensor moments

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF pp.4,13, (20)--(22): dephased tensor moments and their scalar contraction. -/
theorem dephasedTensorMoments (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    momentState d n = (Matrix.diagonal ∘ Matrix.diag)
      (((risingDimension d n)⁻¹ : ℂ) • ∑ s : Equiv.Perm (Fin n), Schur.tensorPermutation d n s) ∧
    (∀ a : Fin n → Fin d,
      (∫ p, ∏ k, p (a k) ∂simplexLaw (Fin d)) =
        (risingDimension d n)⁻¹ * ∑ s : Equiv.Perm (Fin n),
          ∏ k, (if a k = a (s k) then (1 : ℝ) else 0)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
