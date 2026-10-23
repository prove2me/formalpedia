-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P50_hermiticity_criteria
-- name    : QAlgorithms.Papers.Independent.Dependency50.P50.hermiticity_criteria
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:25:22.368624+00:00
-- url     : https://prove2.me/theorems/a3d2f627-4bf4-43ed-9433-86201778ee2a
-- title:
--   Adjoint and arbitrary-basis criteria for Hermiticity preservation
-- statement:
--   Let $n,m>0$, let $\mathcal A=M_n(\mathbb C)$ and $\mathcal B=M_m(\mathbb C)$, and let $T:\mathcal A\to\mathcal B$ be complex-linear. Let $(E_i)_{i\in I}$ be any complex basis of $\mathcal A$. Preserving Hermiticity means mapping every Hermitian input to a Hermitian output. Both equivalences hold:
--
--   $$\begin{aligned}
--   T\text{ preserves Hermiticity}&\iff T(A^*)=T(A)^*\quad\text{for every }A\in\mathcal A,\\
--   T\text{ preserves Hermiticity}&\iff T(E_i^*)=T(E_i)^*\quad\text{for every }i\in I.
--   \end{aligned}$$
--
--   These criteria apply to arbitrary complex bases; neither orthonormality nor Hermiticity of the basis elements is required.
-- source:
--   The Jamio{\l}kowski isomorphism and a conceptionally simple proof for the correspondence between vectors having Schmidt number $k$ and $k$-positive maps, arXiv:quant-ph/0702255v1, PDF p. 4, Lemma 3 (continued on PDF p.5)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P50

/-- PDF pp.4–5, Lemma 3: both the global adjoint criterion and the arbitrary
complex-basis criterion. The basis is neither assumed orthonormal nor Hermitian. -/
theorem hermiticity_criteria {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (T : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)) {I : Type*} (E : Module.Basis I ℂ ((Matrix (Fin n) (Fin n) ℂ))) :
    (PreservesHermiticity T ↔ ∀ A : (Matrix (Fin n) (Fin n) ℂ), T (Aᴴ) = (T A)ᴴ) ∧
      (PreservesHermiticity T ↔ ∀ i : I, T ((E i)ᴴ) = (T (E i))ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P50

end
