-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_measuredDual
-- name    : QAlgorithms.Papers.Independent.Information100.P04.measuredDual
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:27:20.89398+00:00
-- url     : https://prove2.me/theorems/d4630d67-af1b-4f17-93d8-e907df526cca
-- title:
--   Finite attained dual representation of the auxiliary score
-- statement:
--   Let $\rho$ be a normalized bipartite density matrix on nonzero finite-dimensional systems and let $E=(E_j)_j$ be a finite POVM. Put $p_j=\operatorname{Tr}(\rho E_j)$ and $H_j=|E_j^{\Gamma_B}|$. Define $\widetilde\ell(\rho,E)=\sup_{y_j>0}\{\sum_jp_j\log_2 y_j-\log_2\|\sum_jy_jH_j\|_\infty\}$. Then
--
--   $$\widetilde\ell(\rho,E)=\min_{\sigma\ge0,\,\operatorname{Tr}\sigma=1}\sum_jp_j\log_2\frac{p_j}{\operatorname{Tr}(\sigma H_j)}\in\mathbb R.$$
--
--   There exists a normalized density matrix attaining this minimum, and every other normalized density matrix has objective at least this value. Zero-probability terms are zero; a positive numerator with zero denominator gives $+\infty$. This retains both attainment and finiteness of the dual optimum.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 11, Lemma7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 7, PDF p.11: the dual minimum is finite and attained by a normalized density matrix. -/
theorem measuredDual {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (M : Measurement (A × B)) :
    ∃ sigma : Matrix (A × B) (A × B) ℂ, IsDensityMatrix sigma ∧
      dualScore rho sigma M.effect = (ellTilde rho M.effect : EReal) ∧
      ∀ tau : Matrix (A × B) (A × B) ℂ, IsDensityMatrix tau →
        (ellTilde rho M.effect : EReal) ≤ dualScore rho tau M.effect := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
