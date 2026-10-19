-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_rho_star_properties
-- name    : QAlgorithms.Papers.Independent.Information100.P19.rho_star_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:05:38.069354+00:00
-- url     : https://prove2.me/theorems/913e02a2-5716-42b3-bf45-0b0c40671e4f
-- title:
--   Proposition 6.6
-- statement:
--   For the exact qutrit state $\rho_\star=\frac14\sum_{k=1}^4|\psi_k\rangle\langle\psi_k|$ of Eq.(45), both $4\rho_\star$ and $4\rho_\star^{\Gamma_B}$ are rank-four orthogonal projections, with the partial-transpose vector decomposition of Proposition 6.6. Both marginals equal $I_3/3$ and the state is PPT. Its realignment singular multiset is
--   $$\{1/3,(1/6)^{\times5},0^{\times3}\},$$
--   so its trace norm is $7/6$ and the state is entangled. Further, $G=4/9$, the normalized centered singular multiset is $\{(1/4)^{\times5},0^{\times4}\}$, and its normalized trace norm is $5/4$. Multiplicities and zero singular values are retained.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
--
--   The state $\rho_\star$ uses the four unit vectors $\psi_1=(|00\rangle+\sqrt2|21\rangle)/\sqrt3$, $\psi_2=(|01\rangle+\sqrt2|12\rangle)/\sqrt3$, $\psi_3=(\sqrt2|02\rangle-|10\rangle)/\sqrt3$, and $\psi_4=(|11\rangle-\sqrt2|20\rangle)/\sqrt3$, via $\rho_\star=\tfrac14\sum_{j=1}^4|\psi_j\rangle\langle\psi_j|$.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 46, Proposition 6.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 6.6; arXiv:2609.29471v1, PDF pp.46. -/
theorem rho_star_properties  :
    rhoStar.PosSemidef ∧ mass rhoStar=1 ∧
    RankFourProjection ((4:ℂ) • rhoStar) ∧
    RankFourProjection ((4:ℂ) • transposeB rhoStar) ∧
    transposeB rhoStar = (1/4:ℂ) • ∑ k, outer (starTransposeVectors k) ∧
    (transposeB rhoStar).PosSemidef ∧
    marginalA rhoStar = (1/3:ℂ) • 1 ∧ marginalB rhoStar = (1/3:ℂ) • 1 ∧
    singularSpectrum (realign rhoStar) =
      (([1/3] ++ List.replicate 5 (1/6) ++ List.replicate 3 0 : List ℝ) : Multiset ℝ) ∧
    QAlgorithms.traceNorm (realignmentSquare rhoStar)=7/6 ∧
    ¬ QAlgorithms.Entanglement.IsSeparablePositive rhoStar ∧
    G rhoStar=4/9 ∧
    singularSpectrum (realign (((Real.sqrt (G rhoStar))⁻¹:ℂ) • centered rhoStar)) =
      ((List.replicate 5 (1/4) ++ List.replicate 4 0 : List ℝ) : Multiset ℝ) ∧
    QAlgorithms.traceNorm (realignmentSquare (centered rhoStar))/Real.sqrt (G rhoStar)=5/4 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
