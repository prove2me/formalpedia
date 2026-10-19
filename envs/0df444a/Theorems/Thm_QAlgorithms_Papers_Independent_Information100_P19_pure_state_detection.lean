-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_pure_state_detection
-- name    : QAlgorithms.Papers.Independent.Information100.P19.pure_state_detection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:01:33.350563+00:00
-- url     : https://prove2.me/theorems/af715b53-5096-479b-a8f2-899b5137d0ac
-- title:
--   Proposition 6.1
-- statement:
--   Let $\psi$ be a unit bipartite vector and $\rho=|\psi\rangle\langle\psi|$. Each of the three degree-four criteria, and the standard interpolation criterion, is violated exactly when $\psi$ is entangled:
--   $$\widetilde r_1>G,\quad\tfrac32r_1-\tfrac12r_2>1,\quad
--   2(r_1^2-r_2)>(1-r_1)^2,\quad r_1^3>r_2.$$
--   Normalization is essential; this asserts exact detection on all pure states.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 38, Proposition 6.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 6.1; arXiv:2609.29471v1, PDF pp.38, 39. -/
theorem pure_state_detection (a b : ℕ) (ha : 0<a) (hb : 0<b)
    (psi : Fin a × Fin b → ℂ) (hpsi : ∑ i, Complex.normSq (psi i)=1) :
    let X := outer psi
    (0 < rMoment (centered X) 1-G X ↔ ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    (1 < (3/2 : ℝ)*rMoment X 1-(1/2 : ℝ)*rMoment X 2 ↔
      ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    ((1-rMoment X 1)^2 < 2*(rMoment X 1^2-rMoment X 2) ↔
      ¬ QAlgorithms.Entanglement.IsSeparablePositive X) ∧
    (rMoment X 2 < rMoment X 1^3 ↔ ¬ QAlgorithms.Entanglement.IsSeparablePositive X) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
