-- Prove2me | Theorems.Thm_SupportVectorMachines_Kernels_theorem_4_16_symmetric_pd_iff_kernel
-- name    : SupportVectorMachines.Kernels.theorem_4_16_symmetric_pd_iff_kernel
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:00:52.887975+00:00
-- url     : https://prove2.me/theorems/787a70b3-cec1-4fa5-b58d-162c89b63d4d
-- title:
--   Symmetric, positive definite functions are kernels
-- statement:
--   This is Theorem 4.16 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 118): a function $k : X \times X \to \mathbb R$ on a non-empty set $X$ is a kernel if and
--   only if it is symmetric and positive definite.
--
--   $$
--   k \text{ is a kernel} \iff k \text{ is symmetric and positive definite.}
--   $$
--
--   The "only if" direction is an elementary computation from the feature-map definition: if
--   $k(x,x')=\langle\Phi(x),\Phi(x')\rangle$ then symmetry of the inner product gives symmetry of
--   $k$, and $\sum_i\sum_j \alpha_i\alpha_j k(x_j,x_i) = \big\|\sum_i \alpha_i \Phi(x_i)\big\|^2
--   \ge 0$ gives positive definiteness. The "if" direction is the chapter's central construction:
--   given only the two inequalities, it builds an explicit Hilbert space (the completion of the
--   pre-Hilbert space of finite linear combinations of the functions $k(\cdot,x)$) and an explicit
--   feature map ($x \mapsto k(\cdot,x)$, embedded into the completion), with no reference to any
--   space carrying $k$ other than $X$ itself and $\mathbb R$.
--
--   This intrinsic, extrinsic-object-free characterization is what makes positive definiteness
--   the criterion actually used in practice to verify that a proposed similarity function is a
--   valid kernel: one never has to exhibit a feature space, only check a matrix inequality on
--   finitely many points at a time.
--
--   **Formalization Note** `IsKernel` is the feature-map definition of Definition 4.1
--   specialized to $\mathbb K = \mathbb R$; `Symmetric` and `PositiveDefinite` are Definition
--   4.15. $X$ is assumed non-empty, matching Definition 4.1's own standing hypothesis.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 118, Theorem 4.16

import Mathlib
import Definitions.Def_SupportVectorMachines_Kernels_IsKernel
import Definitions.Def_SupportVectorMachines_Kernels_PositiveDefinite

namespace SupportVectorMachines.Kernels

/-- Theorem 4.16 (Symmetric, positive definite functions are kernels), p. 118: a function
`k : X × X → ℝ` is a kernel if and only if it is symmetric and positive definite. -/
theorem theorem_4_16_symmetric_pd_iff_kernel {X : Type*} [Nonempty X] (k : X → X → ℝ) :
    IsKernel k ↔ Symmetric k ∧ PositiveDefinite k := by sorry

end SupportVectorMachines.Kernels
