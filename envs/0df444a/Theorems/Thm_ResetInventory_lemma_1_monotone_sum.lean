-- Prove2me | Theorems.Thm_ResetInventory_lemma_1_monotone_sum
-- name    : ResetInventory.lemma_1_monotone_sum
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:19:43.820978+00:00
-- url     : https://prove2.me/theorems/a68ac39f-e5d9-4e48-a5c3-52d134b0ecc9
-- title:
--   Lemma 1 — $f+\lambda g$ is non-decreasing and continuous
-- statement:
--   **Lemma 1.** Consider two functions $f$ and $g$ on a compact interval $[a,b]$. Suppose that $f$ is differentiable, with derivative bounded below by a positive constant, $D_xf(x)\ge M>0$, and that $g$ is Lipschitz continuous with constant $L\ge0$. Then for every fixed $\lambda$ with $0\le\lambda\le M/L$, the function
--   $$
--   x\mapsto f(x)+\lambda\,g(x)
--   $$
--   is non-decreasing and continuous on $[a,b]$.
--
--   A function growing at rate at least $M$ absorbs a perturbation with slope at most $\lambda L\le M$. In Proposition 3 this is applied to the derivatives: the derivative of the strongly convex stage cost plus $\gamma$ times the Lipschitz derivative of the expected cost-to-go is non-decreasing.
--
--   Differences from the source:
--   - encoding: 0 ≤ λ ≤ M/L → 0 ≤ λ and λ·L ≤ M; reason: equal when L > 0; at L = 0 the paper's M/L imposes no bound, while Lean's M/0 = 0 would force λ = 0
--   - generalization: f differentiable on [a, b] → f has a derivative within [a, b] at every point of [a, b] (one-sided at a and b); reason: a weaker hypothesis: a function differentiable on [a, b] has such derivatives, and at interior points they coincide
--   - generalization: a compact interval [a, b] → any reals a, b; reason: for a > b the interval is empty and both conclusions hold trivially; for a ≤ b it is the source's statement
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Lemma 1, p.37

import Mathlib

namespace ResetInventory

/-- **Lemma 1** of Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, p.37. Consider two
functions `f` and `g` on a compact interval `[a, b]`. Suppose that `f` is differentiable with
derivative bounded below by a positive constant, `D_x f(x) ≥ M > 0`, and that `g` is Lipschitz
continuous with constant `L ≥ 0`. Then for any fixed `λ` with `0 ≤ λ ≤ M / L`, the function
`f + λ g` is non-decreasing and continuous on `[a, b]`.

**Formalization Note** `λ` is written `lam` (`λ` is a Lean keyword). The bound `λ ≤ M / L` is
written `λ L ≤ M` (equal for `L > 0`; at `L = 0` the paper's `M / L` means no bound, while Lean's
`M / 0 = 0` would force `λ = 0`). Differentiability on `[a, b]` is a derivative `f'` within
`[a, b]` at every point of `[a, b]` (one-sided at the endpoints). `a ≤ b` is not required: for
`a > b` the interval is empty and both claims hold trivially. -/
theorem lemma_1_monotone_sum (a b M L lam : ℝ) (f f' g : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivWithinAt f (f' x) (Set.Icc a b) x)
    (hM : 0 < M) (hf' : ∀ x ∈ Set.Icc a b, M ≤ f' x)
    (hL : 0 ≤ L) (hg : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |g x - g y| ≤ L * |x - y|)
    (hlam0 : 0 ≤ lam) (hlam : lam * L ≤ M) :
    MonotoneOn (fun x => f x + lam * g x) (Set.Icc a b) ∧
      ContinuousOn (fun x => f x + lam * g x) (Set.Icc a b) := by sorry

end ResetInventory
