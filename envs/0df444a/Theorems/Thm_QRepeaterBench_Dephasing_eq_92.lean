-- Prove2me | Theorems.Thm_QRepeaterBench_Dephasing_eq_92
-- name    : QRepeaterBench.Dephasing.eq_92
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:34.759963+00:00
-- url     : https://prove2.me/theorems/f90d91ec-cf45-47b8-87a7-ca9726f6838a
-- title:
--   Eq. (92) — σ̃ = Σ_i (1/d)|i⟩⟨i| ⊗ P_d(|i⟩⟨i|) = Σ_{i,m} (P_m/d)|ii⟩⟨ii| = Σ_i (1/d)|ii⟩⟨ii| is a separable state
-- statement:
--   Let $d\ge2$, $p\in[0,1]$, and let $\tilde\sigma=\sum_{i=0}^{d-1}\frac1d|i\rangle\langle i|\otimes\mathcal P_d(|i\rangle\langle i|)$. Then
--
--   $$\tilde\sigma=\sum_{i,m=0}^{d-1}\frac{P_m(p,d)}{d}|ii\rangle\langle ii|=\sum_{i=0}^{d-1}\frac1d|ii\rangle\langle ii| ,$$
--
--   and $\tilde\sigma$ is a separable state for the cut reference : output, i.e. a finite convex combination of product density matrices.
--
--   The state $\tilde\sigma$ is the candidate separable state whose relative entropy with the Choi matrix bounds the entanglement flux from above.
--
--   **Formalization Note** $|ii\rangle\langle ii|$ is the Kronecker product of the matrix unit $|i\rangle\langle i|$ with itself. Separability is the published `IsSeparableDensity` (finite convex combinations of Kronecker products of density matrices, the first factor being the reference).
-- source:
--   Pirandola & Laurenza, General Benchmarks for Quantum Repeaters, arXiv:1512.04945v2, p. 11, Eq. (92)

import Mathlib
import Definitions.Def_QRepeaterBench_Dephasing_Model

open scoped Matrix ENNReal

namespace QRepeaterBench.Dephasing
theorem eq_92 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : sigmaTilde d p = ∑ i : Fin d, ∑ m : Fin d, ((weight d p m : ℂ) / (d : ℂ)) • Matrix.kronecker (Matrix.single i i (1 : ℂ)) (Matrix.single i i (1 : ℂ)) ∧ sigmaTilde d p = ∑ i : Fin d, ((d : ℂ)⁻¹) • Matrix.kronecker (Matrix.single i i (1 : ℂ)) (Matrix.single i i (1 : ℂ)) ∧ QAlgorithms.Entanglement.IsSeparableDensity (sigmaTilde d p) := by sorry
end QRepeaterBench.Dephasing
