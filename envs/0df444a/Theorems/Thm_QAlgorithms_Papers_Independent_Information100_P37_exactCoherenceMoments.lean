-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_exactCoherenceMoments
-- name    : QAlgorithms.Papers.Independent.Information100.P37.exactCoherenceMoments
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:01:39.921459+00:00
-- url     : https://prove2.me/theorems/c774e7ca-ce8c-4583-8aef-a1dfc3b219cd
-- title:
--   Theorem 3, Exact coherence moments (original paper seed)
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   The first moment, second moment $M_2(U)=\mathbb E X_U^2$, and variance are
--   $$
--   C_U=\frac{\operatorname{Tr}G}{d(d+1)},\qquad M_2(U)=\frac{(\operatorname{Tr}G)^2+2\operatorname{Tr}(G^2)+6\sum_jG_{jj}^2}{D_d},\qquad
--   \Delta_U^2=M_2(U)-\frac{(\operatorname{Tr}G)^2}{d^2(d+1)^2}.
--   $$
--   If $s_j=\sum_iP_{ij}^2$, $S=\sum_js_j$, and $R=\|P^TP\|_F^2$, the second moment also equals $[(d-S)^2+2(d-2S+R)+6\sum_j(1-s_j)^2]/D_d$.
--
--   These identities express actual ensemble moments using computable population-response invariants.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 4, Theorem 3, Exact coherence moments (original paper seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.4, Theorem 3, (24)--(26),(29): exact first and second moments and variance. -/
theorem exactCoherenceMoments [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    let d := (Fintype.card ι : ℝ)
    let G := response U
    let E := conjSuperop U
    cgp E = G.trace / (d * (d + 1)) ∧
    moment E 2 = (G.trace ^ 2 + 2 * (G * G).trace + 6 * diagonalSq G) /
      fourthDenominator (Fintype.card ι) ∧
    cgpd E ^ 2 = (G.trace ^ 2 + 2 * (G * G).trace + 6 * diagonalSq G) /
      fourthDenominator (Fintype.card ι) - G.trace ^ 2 / (d ^ 2 * (d + 1) ^ 2) ∧
    moment E 2 = ((d - totalParticipation U) ^ 2 +
      2 * (d - 2 * totalParticipation U + realFrobeniusSq ((transition U)ᵀ * transition U)) +
      6 * ∑ j, (1 - columnParticipation U j) ^ 2) / fourthDenominator (Fintype.card ι) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
