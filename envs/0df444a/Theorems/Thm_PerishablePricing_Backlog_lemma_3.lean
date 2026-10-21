-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_lemma_3
-- name    : PerishablePricing.Backlog.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:27:15.061995+00:00
-- url     : https://prove2.me/theorems/fae6179c-4309-449f-8626-04fd0b29a7d5
-- title:
--   Lemma 3, p. 287 — the largest minimizer of an L♮-convex function is monotone with bounded sensitivity
-- statement:
--   Let $g(x, \xi)$ be L♮-convex on a set $D \subseteq \mathbb{R}^n \times \mathbb{R}$ and let $f(x) = \min_{\xi} g(x, \xi)$, the minimum over $\xi$ with $(x, \xi) \in D$. Let $\xi(x)$ denote the largest minimizer at $x$, whenever it exists. Then:
--
--   1. if $x \le x'$ and both $\xi(x)$ and $\xi(x')$ exist, then $\xi(x) \le \xi(x')$;
--   2. if $\omega > 0$ and both $\xi(x)$ and $\xi(x + \omega e)$ exist, then
--
--   $$\xi(x + \omega e) \le \xi(x) + \omega.$$
--
--   In the model, this is the mechanism behind the monotonicity and bounded sensitivity of the optimal decisions in Theorem 1.
--
--   **Formalization Note** Real case only. The joint vector $(x, \xi)$ is `fun o => o.elim ξ x : Option ι → ℝ`. "Largest optimal solution (assuming existence)" is encoded by taking the largest minimizers as hypotheses (`IsGreatest` of the set of minimizers of the section) at the points compared; their existence implies $x, x + \omega e \in \mathrm{dom}(f)$. The page's side condition "$\xi(x) + \omega \in \mathrm{dom}(f)$" is a slip for $x + \omega e \in \mathrm{dom}(f)$: $\xi(x) + \omega$ is a scalar while $\mathrm{dom}(f) \subseteq \mathbb{R}^n$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Lemma 3, p. 287 (PDF p. 5)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

namespace PerishablePricing.Backlog

/-- Lemma 3 (p. 287), on a domain. The joint vector `(x, ξ) ∈ ℝⁿ × ℝ` is
`fun o => o.elim ξ x : Option ι → ℝ`. Let `g` be L♮-convex on `D`, and for each `x` let the set
of minimizers of `ξ ↦ g(x, ξ)` over the section `{ξ : (x, ξ) ∈ D}` be
`{ξ : (x, ξ) ∈ D ∧ ∀ ξ', (x, ξ') ∈ D → g(x, ξ) ≤ g(x, ξ')}`. If `ξ(x)` and `ξ(x')` are the largest
minimizers at `x ≤ x'` (assuming they exist), then `ξ(x) ≤ ξ(x')`; and if `ξ(x + ωe)` is the
largest minimizer at `x + ωe` with `ω > 0`, then `ξ(x + ωe) ≤ ξ(x) + ω`. -/
theorem lemma_3 {ι : Type*} [Fintype ι] (D : Set (Option ι → ℝ)) (g : (Option ι → ℝ) → ℝ)
    (hg : LNatConvexOn D g) :
    let argmin : (ι → ℝ) → Set ℝ := fun x =>
      {ξ | (fun o : Option ι => o.elim ξ x) ∈ D ∧
        ∀ ξ', (fun o : Option ι => o.elim ξ' x) ∈ D →
          g (fun o => o.elim ξ x) ≤ g (fun o => o.elim ξ' x)}
    (∀ x x' : ι → ℝ, ∀ ξ ξ' : ℝ, x ≤ x' → IsGreatest (argmin x) ξ →
        IsGreatest (argmin x') ξ' → ξ ≤ ξ') ∧
      (∀ x : ι → ℝ, ∀ ω ξ ξ' : ℝ, 0 < ω → IsGreatest (argmin x) ξ →
        IsGreatest (argmin (x + ω • (1 : ι → ℝ))) ξ' → ξ' ≤ ξ + ω) := by sorry

end PerishablePricing.Backlog
