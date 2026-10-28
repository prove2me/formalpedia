-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_enhanced_strictly_stronger
-- name    : QAlgorithms.Papers.Independent.Information100.P19.enhanced_strictly_stronger
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:51:17.752349+00:00
-- url     : https://prove2.me/theorems/cec3b299-bf9b-42b0-94ef-b207dec96896
-- title:
--   Example 5.2: enhanced criterion is strictly stronger
-- statement:
--   The enhanced realignment bound implies the standard bound for every bipartite density matrix. For the exact two-qubit family $\rho_c=\frac12|00\rangle\langle00|+\frac{1+2c}{4}|\psi_+\rangle\langle\psi_+|+\frac{1-2c}{4}|\psi_-\rangle\langle\psi_-|$, with $\psi_\pm=(|01\rangle\pm|10\rangle)/\sqrt2$ and $0\le c\le1/2$,
--   $$\|R(\rho_c)\|_1=c+1/\sqrt2,\quad\|R(\widetilde\rho_c)\|_1=c+1/8,\quad\sqrt{G(\rho_c)}=3/8.$$
--   Detection occurs respectively for $c>1-1/\sqrt2$ and $c>1/4$, proving strictness.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 28, Example 5.2: enhanced criterion is strictly stronger

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Example 5.2: enhanced criterion is strictly stronger; arXiv:2609.29471v1, PDF pp.28, 29. -/
theorem enhanced_strictly_stronger  :
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef → mass X=1 →
      QAlgorithms.traceNorm (realignmentSquare (centered X)) ≤ Real.sqrt (G X) → QAlgorithms.traceNorm (realignmentSquare X) ≤ 1) ∧
    (∀ c : ℝ, 0≤c → c≤1/2 →
      (rhoC c).PosSemidef ∧ mass (rhoC c)=1 ∧
      QAlgorithms.traceNorm (realignmentSquare (rhoC c)) = c+1/Real.sqrt 2 ∧
      QAlgorithms.traceNorm (realignmentSquare (centered (rhoC c))) = c+1/8 ∧ Real.sqrt (G (rhoC c))=3/8 ∧
      (1 < QAlgorithms.traceNorm (realignmentSquare (rhoC c)) ↔ 1-1/Real.sqrt 2 < c) ∧
      (Real.sqrt (G (rhoC c)) < QAlgorithms.traceNorm (realignmentSquare (centered (rhoC c))) ↔ 1/4<c)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
