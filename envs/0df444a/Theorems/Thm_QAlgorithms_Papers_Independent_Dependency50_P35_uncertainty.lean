-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_uncertainty
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.uncertainty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:06:44.717179+00:00
-- url     : https://prove2.me/theorems/d0bee991-e957-4f85-ab1b-8e01049bebd7
-- title:
--   Theorem 11 (Uncertainty Relation for Conditional Rényi Entropies)
-- statement:
--   Let $\rho_{ABC}\ge0$ have trace one, and let $\alpha,\beta\in(1/2,1)\cup(1,\infty)$ satisfy $1/\alpha+1/\beta=2$. For finite POVMs $\{M_x\}_x$ and $\{N_y\}_y$ on $A$, put $c=\max_{x,y}\|\sqrt{M_x}\sqrt{N_y}\|_{\mathrm{op}}$. Define the cq outputs $\omega_{XB}=\bigoplus_x\operatorname{Tr}_{AC}[M_x\rho_{ABC}]$ and $\eta_{YC}=\bigoplus_y\operatorname{Tr}_{AB}[N_y\rho_{ABC}]$. Then
--
--   $$
--   \widetilde H_\alpha(X|B)_\omega+\widetilde H_\beta(Y|C)_\eta\ge\log_2(1/c).
--   $$
--
--   The norm is the induced Hilbert-space operator norm and is unsquared, exactly as printed on PDF p.14. No purity assumption is imposed; the source presents this as an application of [7].
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 14, Theorem 11 (Uncertainty Relation for Conditional Rényi Entropies)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.14, Theorem 11: the printed overlap norm is UNSQUARED. General finite
POVMs and a mixed normalized tripartite input are allowed. -/
theorem uncertainty {A B C X Y : Type} [Fintype A] [Fintype B] [Fintype C]
    [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq X] [DecidableEq Y]
    (a b : ℝ) (ha : (1/2 : ℝ) < a ∧ a ≠ 1) (hb : (1/2 : ℝ) < b ∧ b ≠ 1)
    (hab : 1/a + 1/b = 2) (rho : Mat (A × (B × C))) (hr : Density rho)
    (M : X → Mat A) (N : Y → Mat A) (hM : POVM M) (hN : POVM N) :
    (Real.logb 2 (1 / measurementOverlap M N) : EReal) ≤
      conditionalRenyi a (marginalAB (measured M rho)) +
      conditionalRenyi b (marginalAC (measured N rho)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
