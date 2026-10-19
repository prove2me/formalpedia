-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_coherenceGenerationMatrix
-- name    : QAlgorithms.Papers.Independent.Information100.P37.coherenceGenerationMatrix
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:02:30.205987+00:00
-- url     : https://prove2.me/theorems/5a893917-244a-4aec-b9f7-614b0abbe2e2
-- title:
--   Proposition 2, Coherence-generation matrix
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   For every simplex population $p$, with $x=p-\mathbf1/d$, the response satisfies
--   $$X_U(p)=p^TGp=x^TGx,\qquad G=G^T,\qquad 0\preceq G\preceq I,\qquad G\mathbf1=0.$$
--   Moreover, $P\mathbf1=P^T\mathbf1=\mathbf1$, and the output diagonal is $Pp$. The inequalities are in the positive semidefinite order.
--
--   This identifies coherence generation with a quadratic response on population imbalances.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 3, Proposition 2, Coherence-generation matrix

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.3, Proposition 2, (13)--(16): response, Loewner bounds and centered form. -/
theorem coherenceGenerationMatrix [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    let P := transition U
    let G := response U
    G.IsSymm ∧ G.PosSemidef ∧ (1 - G).PosSemidef ∧
    G.mulVec (fun _ => 1) = 0 ∧ P.mulVec (fun _ => 1) = (fun _ => 1) ∧
    Pᵀ.mulVec (fun _ => 1) = (fun _ => 1) ∧
    ∀ p, IsPopulation p →
      generated (conjSuperop U) p = quadratic G p ∧
      quadratic G p = quadratic G (centered p) ∧
      (∀ i, (conjSuperop U (inputDensity p) i i).re = (P.mulVec p) i) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
