-- Prove2me | Theorems.Thm_SupportVectorMachines_Kernels_lemma_4_5_sums_of_kernels
-- name    : SupportVectorMachines.Kernels.lemma_4_5_sums_of_kernels
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T22:59:15.170215+00:00
-- url     : https://prove2.me/theorems/a0275e4d-8f55-49cd-b2e5-70e95b851cac
-- title:
--   Lemma 4.5 — nonnegative multiples and sums of kernels are kernels
-- statement:
--   This is Lemma 4.5 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 114): let $X$ be a set, $\alpha \ge 0$, and $k, k_1, k_2$ be kernels on $X$. Then $\alpha k$
--   and $k_1 + k_2$ are also kernels on $X$.
--
--   This says the set of kernels on $X$ is closed under nonnegative scaling and addition — a
--   **cone**, not a vector space: the book notes immediately after this lemma that a *difference*
--   of kernels need not be a kernel (take $k_1, k_2$ with $k_1(x,x) < k_2(x,x)$ at some $x$; a
--   feature map of $k_1-k_2$ would force $0 \le \langle\Phi(x),\Phi(x)\rangle = k_1(x,x)-k_2(x,x)
--   < 0$). The lemma is one of the two basic tools (with Lemma 4.6, products) the book uses
--   throughout the chapter to build non-trivial kernels — e.g. every polynomial with nonnegative
--   coefficients applied to a kernel is again a kernel — without exhibiting a feature map by hand
--   each time.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 114, Lemma 4.5

import Mathlib
import Definitions.Def_SupportVectorMachines_Kernels_IsKernel

namespace SupportVectorMachines.Kernels

/-- Lemma 4.5 (Sums of kernels), p. 114: let `X` be a set, `α ≥ 0`, and `k, k₁, k₂` be kernels
on `X`. Then `αk` and `k₁ + k₂` are also kernels on `X`. -/
theorem lemma_4_5_sums_of_kernels {X : Type*} (α : ℝ) (hα : 0 ≤ α) (k k1 k2 : X → X → ℝ)
    (hk : IsKernel k) (hk1 : IsKernel k1) (hk2 : IsKernel k2) :
    IsKernel (fun x x' => α * k x x') ∧
      IsKernel (fun x x' => k1 x x' + k2 x x') := by sorry

end SupportVectorMachines.Kernels
