-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_regularizedFormula
-- name    : QAlgorithms.Papers.Independent.Information100.P04.regularizedFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:26:37.175005+00:00
-- url     : https://prove2.me/theorems/8946186e-d50e-40b0-821d-84a7b4593510
-- title:
--   Regularized formula for PPT distillable entanglement
-- statement:
--   Let $\rho$ be a density matrix on a finite-dimensional bipartite system $A:B$, with both local dimensions positive. For every finite POVM $E=(E_j)_j$, set $p_j=\operatorname{Tr}(\rho E_j)$ and $\ell(\rho,E)=\sum_{p_j>0}p_j\log_2(p_j/\|E_j^{\Gamma_B}\|_\infty)$. Let $L(\rho)$ be the supremum of this score over all finite POVMs. Partial transpose is taken on $B$ in the fixed product basis, and the norm is the spectral operator norm. Then
--
--   $$E_{d,\mathrm{PPT}}(\rho)=\lim_{n\to\infty}\frac{L(\rho^{\otimes n})}{n}=\sup_{n\ge1}\frac{L(\rho^{\otimes n})}{n}.$$
--
--   Here $E_{d,\mathrm{PPT}}$ is the supremum of rates achievable by PPT channels with Bell overlap tending to one. This identifies the operational rate with the regularized measurement optimization.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 5, Theorem1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 1, PDF pp.5,15–16: operational equality, existence of the regularized limit,
and the positive-block supremum formula. -/
theorem regularizedFormula {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) :
    Tendsto (LLevel rho) atTop (nhds (distillable rho)) ∧
      distillable rho = sSup (Set.range (LLevel rho)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
