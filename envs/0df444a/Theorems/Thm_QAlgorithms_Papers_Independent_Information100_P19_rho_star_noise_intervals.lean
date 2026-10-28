-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_rho_star_noise_intervals
-- name    : QAlgorithms.Papers.Independent.Information100.P19.rho_star_noise_intervals
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:06:59.885906+00:00
-- url     : https://prove2.me/theorems/66a23a49-fe77-4310-94be-29d54afbded5
-- title:
--   §6.5 unnumbered: exact noisy rhoStar detection intervals
-- statement:
--   For $0\le p\le1$, let $\rho_\star(p)=p\rho_\star+(1-p)I_9/9$. It is PPT, with marginal states $I_3/3$, $G=4/9$, partial-transpose eigenvalues $p/4+(1-p)/9$ four times and $(1-p)/9$ five times, realignment singular values $1/3,p/6$ five times and three zeros, and normalized centered singular values $p/4$ five times and four zeros. Each of standard realignment, enhanced realignment and centered interpolation detects exactly when
--   $$p>4/5.$$
--   The moments are $r_1=(4+5p^2)/36$, $r_2=(16+5p^4)/1296$, and
--   $$r_2-r_1^3=(512-240p^2-120p^4-125p^6)/46656>0.$$
--   Thus standard interpolation never detects the family. Spectra are full multisets, valid also at $p=0$.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
--
--   The state $\rho_\star$ uses the four unit vectors $\psi_1=(|00\rangle+\sqrt2|21\rangle)/\sqrt3$, $\psi_2=(|01\rangle+\sqrt2|12\rangle)/\sqrt3$, $\psi_3=(\sqrt2|02\rangle-|10\rangle)/\sqrt3$, and $\psi_4=(|11\rangle-\sqrt2|20\rangle)/\sqrt3$, via $\rho_\star=\tfrac14\sum_{j=1}^4|\psi_j\rangle\langle\psi_j|$.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 47, §6.5 unnumbered: exact noisy rhoStar detection intervals

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- §6.5 unnumbered: exact noisy rhoStar detection intervals; arXiv:2609.29471v1, PDF pp.47. -/
theorem rho_star_noise_intervals (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    let X := noisyStar p
    X.PosSemidef ∧ mass X=1 ∧ (transposeB X).PosSemidef ∧
    eigenSpectrum (transposeB X) =
      ((List.replicate 4 (p/4+(1-p)/9) ++ List.replicate 5 ((1-p)/9) : List ℝ) : Multiset ℝ) ∧
    marginalA X=(1/3:ℂ) • 1 ∧ marginalB X=(1/3:ℂ) • 1 ∧ G X=4/9 ∧
    singularSpectrum (realign X) =
      (([1/3] ++ List.replicate 5 (p/6) ++ List.replicate 3 0 : List ℝ) : Multiset ℝ) ∧
    singularSpectrum (realign (((Real.sqrt (G X))⁻¹:ℂ) • centered X)) =
      ((List.replicate 5 (p/4) ++ List.replicate 4 0 : List ℝ) : Multiset ℝ) ∧
    (1<QAlgorithms.traceNorm (realignmentSquare X) ↔ 4/5<p) ∧
    (Real.sqrt (G X)<QAlgorithms.traceNorm (realignmentSquare (centered X)) ↔ 4/5<p) ∧
    (rMoment (centered X) 2*G X<rMoment (centered X) 1^3 ↔ 4/5<p) ∧
    rMoment X 1=(4+5*p^2)/36 ∧ rMoment X 2=(16+5*p^4)/1296 ∧
    rMoment X 2-rMoment X 1^3=(512-240*p^2-120*p^4-125*p^6)/46656 ∧
    0<rMoment X 2-rMoment X 1^3 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
