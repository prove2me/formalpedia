-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_generalPSDDecomposition
-- name    : QAlgorithms.Papers.Independent.Information100.P37.generalPSDDecomposition
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-19T11:21:50.283839+00:00
-- url     : https://prove2.me/theorems/9d612652-f2d2-467f-b634-2d7efba32c73
-- title:
--   Appendix C, Eqs. (C1)–(C4): generic PSD fluctuation decomposition
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let $d\ge2$ and let $G$ now be any real positive semidefinite matrix satisfying $G\mathbf1=0$. Define $t=\operatorname{Tr}G$ and $A=G-tH_d/(d-1)$. Then $A\mathbf1=0$, $\operatorname{Tr}A=0$, and
--   $$\operatorname{Tr}(G^2)=\frac{t^2}{d-1}+\|A\|_F^2,\qquad \sum_iG_{ii}^2=\frac{t^2}{d}+\sum_iA_{ii}^2,$$
--   $$\operatorname{Var}_{\nu_d}(p^TGp)=\frac{4t^2}{(d-1)(d+1)^2(d+2)(d+3)}+\frac{2\|A\|_F^2+6\sum_iA_{ii}^2}{D_d}.$$
--   Equality with the first term alone holds if and only if $A=0$. There is no upper bound $G\preceq I$ among the assumptions.
--
--   The algebraic fluctuation decomposition holds for a larger class of PSD responses.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 13, Appendix C, Eqs. (C1)–(C4): generic PSD fluctuation decomposition

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF pp.13--14, Appendix C, (C1)--(C4): generic PSD decomposition without G<=I. -/
theorem generalPSDDecomposition (hd : 2 ≤ Fintype.card ι) (G : Matrix ι ι ℝ)
    (hp : G.PosSemidef) (hz : G.mulVec (fun _ => 1) = 0) :
    let d := (Fintype.card ι : ℝ)
    let A := anisotropy G
    let v := ∫ p, (quadratic G p - ∫ q, quadratic G q ∂simplexLaw ι) ^ 2 ∂simplexLaw ι
    A.mulVec (fun _ => 1) = 0 ∧ A.trace = 0 ∧
    (G * G).trace = G.trace ^ 2 / (d - 1) + realFrobeniusSq A ∧
    diagonalSq G = G.trace ^ 2 / d + diagonalSq A ∧
    v = 4 * G.trace ^ 2 / ((d - 1) * (d + 1) ^ 2 * (d + 2) * (d + 3)) +
      (2 * realFrobeniusSq A + 6 * diagonalSq A) / fourthDenominator (Fintype.card ι) ∧
    (v = 4 * G.trace ^ 2 / ((d - 1) * (d + 1) ^ 2 * (d + 2) * (d + 3)) ↔ A = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
