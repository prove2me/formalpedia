-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_lemma_2
-- name    : PerishablePricing.Backlog.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:59.938225+00:00
-- url     : https://prove2.me/theorems/c0cacb97-dccb-4c35-8884-5dbe13ee3410
-- title:
--   Lemma 2, p. 287 — minimizing an L♮-convex function over an L♮-convex set preserves L♮-convexity
-- statement:
--   Let $\mathcal{A} \subseteq \mathbb{R}^n \times \mathbb{R}^m$ be an L♮-convex set and let $f$ be L♮-convex on $\mathcal{A}$. Let
--
--   $$\pi(\mathcal{A}) = \{x \in \mathbb{R}^n : (x, y) \in \mathcal{A} \text{ for some } y\}$$
--
--   and suppose that for every $x \in \pi(\mathcal{A})$ the values $f(x, y)$, $(x, y) \in \mathcal{A}$, are bounded below. Then the function
--
--   $$g(x) = \inf_{(x, y) \in \mathcal{A}} f(x, y)$$
--
--   is L♮-convex on $\pi(\mathcal{A})$; in particular $\pi(\mathcal{A})$ is an L♮-convex set.
--
--   This preservation property is the heart of the inductive argument of Theorem 1: it carries L♮-concavity from $\phi_t$ to $g_t$ and from $G_t$ to $f_t$ (applied to the negatives).
--
--   **Formalization Note** Real case only. A vector of $\mathbb{R}^n \times \mathbb{R}^m$ is `Sum.elim x y : ι ⊕ κ → ℝ` over finite index types. The paper's hypothesis "$g(x) \ne -\infty$ for any $x$" is the lower boundedness of each nonempty section; off $\pi(\mathcal{A})$ the paper's $g$ is $+\infty$, so $\pi(\mathcal{A})$ is exactly the effective domain of $g$ and the conclusion is stated there. The infimum is `sInf` of the image of the nonempty, bounded-below section, so it is the true infimum.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Lemma 2, p. 287 (PDF p. 5)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

namespace PerishablePricing.Backlog

/-- Lemma 2 (p. 287), on a domain. The joint vector `w : ι ⊕ κ → ℝ` is `(x, y) ∈ ℝⁿ × ℝᵐ`,
`w = Sum.elim x y`. Let `f` be L♮-convex on the L♮-convex set `𝒜`, and suppose that for every `x`
in the projection `π(𝒜) = {x : ∃ y, (x, y) ∈ 𝒜}` the values `f(x, y)`, `(x, y) ∈ 𝒜`, are bounded
below (`g(x) ≠ −∞`). Then `g(x) = inf_{(x,y) ∈ 𝒜} f(x, y)` is L♮-convex on `π(𝒜)`, which is the
effective domain of `g` (in particular `π(𝒜)` is an L♮-convex set). -/
theorem lemma_2 {ι κ : Type*} [Fintype ι] [Fintype κ] (𝒜 : Set (ι ⊕ κ → ℝ))
    (f : (ι ⊕ κ → ℝ) → ℝ) (hf : LNatConvexOn 𝒜 f)
    (hbdd : ∀ x : ι → ℝ, (∃ y : κ → ℝ, Sum.elim x y ∈ 𝒜) →
      BddBelow ((fun y => f (Sum.elim x y)) '' {y | Sum.elim x y ∈ 𝒜})) :
    LNatConvexOn {x : ι → ℝ | ∃ y : κ → ℝ, Sum.elim x y ∈ 𝒜}
      (fun x => sInf ((fun y => f (Sum.elim x y)) '' {y | Sum.elim x y ∈ 𝒜})) := by sorry

end PerishablePricing.Backlog
