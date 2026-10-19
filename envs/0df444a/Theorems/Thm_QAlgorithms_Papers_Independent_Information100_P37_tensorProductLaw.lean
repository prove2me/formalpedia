-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_tensorProductLaw
-- name    : QAlgorithms.Papers.Independent.Information100.P37.tensorProductLaw
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:12:14.593749+00:00
-- url     : https://prove2.me/theorems/14af783a-a4bf-49f0-bdd4-4ef21c5c4b7e
-- title:
--   Proposition 12, Tensor-product law
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let unitary $U,V$ act on dimensions $m,n\ge1$, using the product reference basis. Put $G_U=I-P_U^TP_U$, $G_V=I-P_V^TP_V$, $t_U=\operatorname{Tr}G_U$, and $t_V=\operatorname{Tr}G_V$. Then
--   $$G_{U\otimes V}=G_U\otimes I+I\otimes G_V-G_U\otimes G_V,$$
--   $$C_{U\otimes V}=\frac{nt_U+mt_V-t_Ut_V}{mn(mn+1)}.$$
--   The joint mean is taken over the full $mn$-dimensional population simplex, rather than independently chosen subsystem populations.
--
--   The product law propagates average coherence generation through parallel composition.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 7, Proposition 12, Tensor-product law

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.7, Proposition 12: response and full joint-simplex mean of a tensor product. -/
theorem tensorProductLaw [Nonempty ι] [Nonempty κ] (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup κ ℂ) :
    response (Matrix.kronecker U V) = Matrix.kronecker (response U) 1 +
      Matrix.kronecker 1 (response V) - Matrix.kronecker (response U) (response V) ∧
    cgp (conjSuperop (Matrix.kronecker U V)) =
      ((Fintype.card κ : ℝ) * (response U).trace + (Fintype.card ι : ℝ) * (response V).trace -
        (response U).trace * (response V).trace) /
      ((Fintype.card ι : ℝ) * Fintype.card κ * ((Fintype.card ι : ℝ) * Fintype.card κ + 1)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
