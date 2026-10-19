-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapX01_separable_partialTransposeFirst_posSemidef
-- name    : QAlgorithms.Papers.RoadmapX01.separable_partialTransposeFirst_posSemidef
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:05:48.056988+00:00
-- url     : https://prove2.me/theorems/98ce6cfe-ba5f-4790-901a-dc96bdfe357d
-- title:
--   Peres criterion: separability implies positive partial transpose
-- statement:
--   Let $I$ and $J$ index orthonormal bases of two nonempty finite-dimensional complex Hilbert spaces, with no requirement that their dimensions agree. Let $\rho$ be a density matrix on their tensor product, so $\rho$ is positive semidefinite and $\operatorname{Tr}\rho=1$. Suppose it is separable: for some finite ensemble of density matrices $A_a$ on the first subsystem and $B_a$ on the second, and real weights $w_a\ge0$ summing to one, $\rho=\sum_a w_a A_a\otimes B_a$. Define its first-subsystem partial transpose by $\sigma_{(i,j),(i',j')}=\rho_{(i',j),(i,j')}$. Then
--
--   $$
--   \sigma=\rho^{T_I}\succeq0.
--   $$
--
--   Equivalently, all eigenvalues of the Hermitian matrix $\sigma$ are nonnegative. This is a necessary condition for separability, with no assertion of a converse.
--
--   **Formalization Note** The unspecified ensemble in Eq. (1) is represented by an arbitrary finite ensemble in the paper's finite-dimensional setting. Allowing zero weights is equivalent to the printed positive-weight convention after deleting zero-weight terms; normalization excludes an empty ensemble.
-- source:
--   Separability Criterion for Density Matrices, arXiv:quant-ph/9604005v2, Unnumbered conclusion following Eq. (6); definitions in Eqs. (1)–(3), PDF p. 2, PDF p. 3. https://arxiv.org/abs/quant-ph/9604005v2 . PDF SHA-256: 6574d1af38e331a5ed4f7c58673855e1e580eb96d79fa52338f18cdc22d43998.

import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
set_option autoImplicit false

open scoped ComplexOrder

namespace QAlgorithms.Papers.RoadmapX01

/-- Peres, *Separability Criterion for Density Matrices*, arXiv:quant-ph/9604005v2,
PDF pp. 2–3: the unnumbered conclusion immediately following Eq. (6), with
separability defined by Eq. (1) and first-subsystem partial transpose by Eq. (3).
Every separable density matrix on two nonempty finite-dimensional subsystems
has positive semidefinite partial transpose. -/
theorem separable_partialTransposeFirst_posSemidef
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (rho : Matrix (I × J) (I × J) ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho)
    (hsep : QAlgorithms.Entanglement.IsSeparableDensity rho) :
    (QAlgorithms.Entanglement.partialTransposeFirst rho).PosSemidef := by sorry

end QAlgorithms.Papers.RoadmapX01
