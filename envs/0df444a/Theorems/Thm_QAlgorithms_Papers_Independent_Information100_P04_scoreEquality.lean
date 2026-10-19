-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_scoreEquality
-- name    : QAlgorithms.Papers.Independent.Information100.P04.scoreEquality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:31:40.819989+00:00
-- url     : https://prove2.me/theorems/83bcb37f-168e-4374-9617-9f95028e0b6e
-- title:
--   Equality criterion for the two measured scores
-- statement:
--   Let $\rho$ be a bipartite density matrix on nonzero finite-dimensional systems and let $E=(E_j)_j$ be a finite POVM. Put $p_j=\operatorname{Tr}(\rho E_j)$ and $H_j=|E_j^{\Gamma_B}|$. The scores $\ell$ and $\widetilde\ell$ are those in (38) and (35). Then
--
--   $$\widetilde\ell(\rho,E)=\ell(\rho,E)\quad\Longleftrightarrow\quad\exists v\ne0:\ H_jv=\|E_j^{\Gamma_B}\|_\infty v\ \text{for every }j\text{ with }p_j>0.$$
--
--   Equivalently, the maximal-eigenvalue eigenspaces of the positive operators $H_j$ for positive-probability outcomes have a nonzero common intersection. This identifies precisely when passing to individual operator norms loses nothing.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 12, eq38-equality

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Equality characterization in (38), PDF p.12: common maximal eigenspaces of ABSOLUTE
partially transposed effects, and only for outcomes of positive probability. -/
theorem scoreEquality {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (M : Measurement (A × B)) :
    ellTilde rho M.effect = ell rho M.effect ↔
      ∃ v : (A × B) → ℂ, v ≠ 0 ∧ ∀ j, 0 < effectProb (M.effect j) rho →
        (absOp (gamma (M.effect j))).mulVec v = (specNorm (gamma (M.effect j)) : ℂ) • v := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
