-- Prove2me | Theorems.Thm_PfisterCEP_hasDerivAt_smul_unique
-- name    : PfisterCEP.hasDerivAt_smul_unique
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:26:05.77161+00:00
-- url     : https://prove2.me/theorems/db9573a9-1855-4ed6-af49-ad994c51192c
-- title:
--   Solutions of $\dot f=cf$ are $f(t)=e^{ct}f(0)$ (locally convex, Hausdorff)
-- statement:
--   Let $A$ be a complex vector space with a Hausdorff, locally convex vector-space topology, let $c$ be real and $f:\mathbb R\to A$ satisfy
--
--   $$f'(t)=c\,f(t)\qquad\text{for every }t\in\mathbb R .$$
--
--   Then $f(t)=e^{ct}f(0)$ for every real $t$.
--
--   This is the step by which the paper passes from the eigen-equations of the Heisenberg system to the solutions $\mathbf P(t)=\mathbf P(0)e^{-N\kappa t}$ and $X_{kl}(t)=X_{kl}(0)$: an operator on which the generator acts by a scalar evolves by the corresponding exponential, and by nothing else. The space is not assumed normed, because the canonical commutation relations have no nonzero solution in a normed algebra.
--
--   **Formalization Note** $A$ carries no multiplication in this statement; $e^{ct}$ is a real number acting through $\mathbb R\subset\mathbb C$. The real scalar action is restricted from $\mathbb C$, and its continuity is listed as a separate instance because Mathlib does not infer it.
--
--   Differences from the source:
--
--   - reading: 'this eigensystem yields the following solution to the quantum evolution' (uniqueness of the solution used, not stated) → uniqueness of solutions of $f'=cf$ in a Hausdorff locally convex complex space; reason: the paper solves the linear Heisenberg system and uses, without stating it, that the exponential is the only solution
--   - encoding: no topology named → Hausdorff locally convex topology over $\mathbb R$ (restricted from $\mathbb C$), `ContinuousSMul ℝ A` listed separately; reason: the paper names no framework; continuity of the real action follows from `ContinuousSMul ℂ A`, so the extra instance excludes nothing
-- source:
--   Pfister, Graph states and carrier-envelope phase squeezing, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column ("this eigensystem yields the following solution to the quantum evolution"); supporting step, not stated in the paper

import Mathlib

namespace PfisterCEP

/-- **Solutions of `ẋ = c x` are exponentials.**
O. Pfister, *Graph states and carrier-envelope phase squeezing*, arXiv:quant-ph/0701104v2, Sec. b, p.2, left column ("this eigensystem yields the following solution to the quantum
evolution"); used again for `H₃` (p.2, right column). Supporting step, not stated in the paper.

In a Hausdorff locally convex complex topological vector space, if `f : ℝ → A` satisfies
`f'(t) = c f(t)` for every real `t` (with `c` real), then `f(t) = e^{ct} f(0)` for every `t`.

**Formalization Note** `A` carries no multiplication here; the scalar `e^{ct}` is a real number
cast to `ℂ`. Local convexity over `ℝ` (with the ℝ-structure restricted from `ℂ`) and the Hausdorff
property make continuous linear functionals separate points. `ContinuousSMul ℝ A` is listed
separately because Mathlib does not infer it; it follows from `ContinuousSMul ℂ A`. -/
theorem hasDerivAt_smul_unique {A : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℂ A] [ContinuousSMul ℝ A] [T2Space A] [LocallyConvexSpace ℝ A] (f : ℝ → A) (c : ℝ) (hf : ∀ t : ℝ, HasDerivAt f (((c : ℝ) : ℂ) • f t) t) : ∀ t : ℝ, f t = ((Real.exp (c * t) : ℝ) : ℂ) • f 0 := by sorry

end PfisterCEP
