-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_classical_divergence
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.classical_divergence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:04:04.082324+00:00
-- url     : https://prove2.me/theorems/c36f43fa-06f6-488b-8d1e-c590e4da2f25
-- title:
--   Block decomposition with a classical register
-- statement:
--   Let $\alpha\in(0,1)\cup(1,\infty)$, let $p,q$ be probability distributions on a finite set $Y$, and let $\rho_A^y,\sigma_A^y$ be normalized PSD states. Form $\rho_{AY}=\bigoplus_y p_y\rho_A^y$ and $\sigma_{AY}=\bigoplus_y q_y\sigma_A^y$. Then
--
--   $$
--   \widetilde D_\alpha(\rho_{AY}\|\sigma_{AY})=\frac1{\alpha-1}\log_2\sum_y B_y.
--   $$
--
--   Here $B_y=0$ if $p_y=0$; if $p_y>0$ and $\alpha>1$, it is $+\infty$ when $q_y=0$ or $\sigma_A^y$ does not dominate $\rho_A^y$. Otherwise it is $p_y^\alpha q_y^{1-\alpha}\operatorname{Tr}[( (\sigma_A^y)^{(1-\alpha)/(2\alpha)}\rho_A^y(\sigma_A^y)^{(1-\alpha)/(2\alpha)})^\alpha]$. Scalar logarithms retain their extended limits. On finite nonzero blocks this is exactly the printed exponential-divergence formula, and the guarded expression also covers all zero weights.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 12, Block decomposition with a classical register

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.12: classical-register divergence decomposition. Each weighted block is
evaluated before the logarithm, preserving all zero-weight and infinite cases. -/
theorem classical_divergence {A Y : Type} [Fintype A] [Fintype Y]
    [DecidableEq A] [DecidableEq Y] (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    (p q : Distribution Y)
    (rho sigma : Y → Mat A) (hr : ∀ y, Density (rho y)) (hs : ∀ y, Density (sigma y)) :
    divergence a (cq p.val rho) (cq q.val sigma) =
      ((1 / (a-1) : ℝ) : EReal) * elogNN (∑ y, blockTerm a (p.val y) (q.val y) (rho y) (sigma y)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
