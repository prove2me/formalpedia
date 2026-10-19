-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_binomial_minorants_converge
-- name    : QAlgorithms.Papers.Independent.Information100.P19.binomial_minorants_converge
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:58:53.087249+00:00
-- url     : https://prove2.me/theorems/ba6a907c-43fe-4d01-b31a-2d0dda1d8752
-- title:
--   §5.2 unnumbered: binomial minorants, monotonicity, and convergence
-- statement:
--   For $m\ge1$, define $f_m(x)=x\sum_{a=0}^{m-1}(2a)!\,(1-x)^a/(4^a(a!)^2)$. On $[0,1]$,
--   $$f_m(x)\le\sqrt x,\qquad f_m(x)\le f_{m+1}(x),\qquad f_m(x)\longrightarrow\sqrt x.$$
--   Finite sums over squared singular values therefore converge increasingly to their trace norm. This applies to density matrices and to the centered realignment scaled by $\sqrt G$ when $G>0$ and $\widetilde r_1\le G$, which ensures every normalized squared singular value lies in $[0,1]$. If $\widetilde r_1>G$, the first centered test already detects the state. For PSD inputs with $G=0$, the centered operator is zero. These are the nested binomial minorants, independently of weighted optimizer choices.
--
--   Here $R(X)_{ik,jl}=X_{ij,kl}$ is realignment, $r_k(X)=\operatorname{Tr}[(R(X)R(X)^*)^k]$, and all traces are ordinary unnormalized matrix traces. We write $t=\operatorname{Tr}X$, $X_A=\operatorname{Tr}_B X$, $X_B=\operatorname{Tr}_A X$, $\widetilde X=tX-X_A\otimes X_B$, $\widetilde r_k=r_k(\widetilde X)$, and $G=(t^2-\operatorname{Tr}X_A^2)(t^2-\operatorname{Tr}X_B^2)$. The notation $q_k$ means $\operatorname{Tr}[(X^{\Gamma_B})^k]$, where $\Gamma_B$ transposes the B factor.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 34, §5.2 unnumbered: binomial minorants, monotonicity, and convergence

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- §5.2 unnumbered: binomial minorants, monotonicity, and convergence; arXiv:2609.29471v1, PDF pp.34, 35, 44. -/
theorem binomial_minorants_converge  :
    (∀ x ∈ Set.Icc (0:ℝ) 1, (∀ m : ℕ, 1 ≤ m → binomial m x ≤ Real.sqrt x) ∧
      (∀ m : ℕ, 1 ≤ m → binomial m x ≤ binomial (m+1) x) ∧
      Tendsto (fun m => binomial m x) atTop (nhds (Real.sqrt x))) ∧
    (∀ N : ℕ, ∀ s : Fin N → ℝ, (∀ i, s i ∈ Set.Icc (0:ℝ) 1) →
      Tendsto (fun m => ∑ i, binomial m (s i^2)) atTop (nhds (∑ i, s i))) ∧
    (∀ a b, 0<a → 0<b → ∀ X : Bip a b, X.PosSemidef → mass X=1 →
      Tendsto (fun m => ((singularSpectrum (realign X)).map
        (fun s => binomial m (s^2))).sum) atTop (nhds (QAlgorithms.traceNorm (realignmentSquare X))) ∧
      (G X=0 → centered X=0) ∧
      (G X<rMoment (centered X) 1 → defect 1 X<0) ∧
      (0<G X → rMoment (centered X) 1 ≤ G X → Tendsto (fun m => ((singularSpectrum
        (realign (((Real.sqrt (G X))⁻¹ : ℂ) • centered X))).map
          (fun s => binomial m (s^2))).sum) atTop
            (nhds (QAlgorithms.traceNorm (realignmentSquare (centered X))/Real.sqrt (G X))))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
