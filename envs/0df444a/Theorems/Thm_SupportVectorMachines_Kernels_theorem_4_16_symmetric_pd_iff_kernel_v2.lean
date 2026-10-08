-- Prove2me | Theorems.Thm_SupportVectorMachines_Kernels_theorem_4_16_symmetric_pd_iff_kernel_v2
-- name    : SupportVectorMachines.Kernels.theorem_4_16_symmetric_pd_iff_kernel_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:20.474224+00:00
-- url     : https://prove2.me/theorems/7d5e25f1-3b04-4491-865c-3c9906cb816e
-- title:
--   Symmetric, positive definite functions are kernels (feature space in the universe of $X$)
-- statement:
--   This is Theorem 4.16 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 118): a function $k : X \times X \to \mathbb R$ on a non-empty set $X$ is a kernel if and only if it is symmetric and positive definite,
--   $$
--   k \text{ is a kernel} \iff k \text{ is symmetric and positive definite.}
--   $$
--
--   The "only if" direction follows from $k(x,x') = \langle\Phi(x),\Phi(x')\rangle$: symmetry of the real inner product, and $\sum_{i,j}\alpha_i\alpha_j k(x_j,x_i) = \|\sum_i \alpha_i\Phi(x_i)\|^2 \ge 0$. The "if" direction builds the feature space intrinsically: the completion of the pre-Hilbert space of finite linear combinations of the functions $k(\cdot,x)$, with feature map $x \mapsto k(\cdot,x)$.
--
--   **Formalization Note.** The mathematics of the retired version was correct; it was refuted only by a Lean universe artefact: `IsKernel` fixed the feature space to universe $0$ while $X$ ranged over every universe, so for an $X$ too large to embed in universe $0$ (`Ordinal.{0}`) the Kronecker kernel was symmetric and positive definite but had no universe-$0$ feature space. The corrected `IsKernel` quantifies the feature space over the universe of $X$, where the book's construction lives (and any feature space in a larger universe can be replaced by the closed span of $\Phi(X)$, isometric to one in the universe of $X$); `Symmetric` and `PositiveDefinite` are Definition 4.15 unchanged, and $X$ is non-empty as in Definition 4.1.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 118, Theorem 4.16

import Mathlib
import Definitions.Def_SupportVectorMachines_Kernels_IsKernel_v2
import Definitions.Def_SupportVectorMachines_Kernels_PositiveDefinite

universe u

namespace SupportVectorMachines.Kernels

/-- Theorem 4.16 (Symmetric, positive definite functions are kernels), Steinwart & Christmann,
*Support Vector Machines*, Springer 2008, p. 118: a function `k : X × X → ℝ` on a non-empty set
`X` is a kernel if and only if it is symmetric and positive definite. Here `IsKernel` quantifies
the feature space over the same universe as `X` (the retired `IsKernel` fixed it to universe `0`
while `X` was arbitrary, a Lean universe artefact that made the "if" direction refutable for a
large `X`; the mathematics is unchanged). Corrected version of
`theorem_4_16_symmetric_pd_iff_kernel`. -/
theorem theorem_4_16_symmetric_pd_iff_kernel_v2 {X : Type u} [Nonempty X] (k : X → X → ℝ) :
    IsKernel k ↔ Symmetric k ∧ PositiveDefinite k := by sorry

end SupportVectorMachines.Kernels
