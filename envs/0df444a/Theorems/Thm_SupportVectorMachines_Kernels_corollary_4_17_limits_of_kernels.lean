-- Prove2me | Theorems.Thm_SupportVectorMachines_Kernels_corollary_4_17_limits_of_kernels
-- name    : SupportVectorMachines.Kernels.corollary_4_17_limits_of_kernels
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:00:07.726316+00:00
-- url     : https://prove2.me/theorems/32f275fb-8116-4daf-a7f3-ebe6ab3bf0f4
-- title:
--   Corollary 4.17 — a pointwise limit of kernels is a kernel
-- statement:
--   This is Corollary 4.17 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 119): let $(k_n)$ be a sequence of kernels on a set $X$ that converges pointwise to a
--   function $k : X \times X \to \mathbb R$, i.e. $\lim_{n\to\infty} k_n(x,x') = k(x,x')$ for all
--   $x,x' \in X$. Then $k$ is a kernel on $X$.
--
--   This is one of the most useful corollaries of Theorem 4.16: exhibiting a feature map for a
--   pointwise limit of kernels can be very difficult directly, but symmetry and positive
--   definiteness both pass to a pointwise limit for free (a finite sum of limits is the limit of
--   the finite sums), so the characterization theorem turns an analytic limiting argument into a
--   kernel-construction tool.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 119, Corollary 4.17

import Mathlib
import Definitions.Def_SupportVectorMachines_Kernels_IsKernel

namespace SupportVectorMachines.Kernels

/-- Corollary 4.17 (Limits of kernels are kernels), p. 119: let `(kₙ)` be a sequence of kernels
on the set `X` that converges pointwise to a function `k : X × X → ℝ`, i.e.
`limₙ→∞ kₙ(x,x') = k(x,x')` for all `x, x' ∈ X`. Then `k` is a kernel on `X`. -/
theorem corollary_4_17_limits_of_kernels {X : Type*} (kn : ℕ → X → X → ℝ) (k : X → X → ℝ)
    (hkn : ∀ n, IsKernel (kn n))
    (hlim : ∀ x x' : X, Filter.Tendsto (fun n => kn n x x') Filter.atTop (nhds (k x x'))) :
    IsKernel k := by sorry

end SupportVectorMachines.Kernels
