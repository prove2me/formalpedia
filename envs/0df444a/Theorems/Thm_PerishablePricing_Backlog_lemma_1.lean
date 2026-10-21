-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_lemma_1
-- name    : PerishablePricing.Backlog.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:25:21.228637+00:00
-- url     : https://prove2.me/theorems/fe829a9f-2fd0-409d-805d-5d820d236a73
-- title:
--   Lemma 1, p. 287 — g(x, ξ) = f(x − ξe) inherits L♮-convexity
-- statement:
--   Let $f$ be L♮-convex on a set $\mathcal{V} \subseteq \mathbb{R}^n$. Define, on $\mathbb{R}^n \times \mathbb{R}$,
--
--   $$g(x, \xi) = f(x - \xi e).$$
--
--   Then $g$ is L♮-convex on its domain $\{(x, \xi) : x - \xi e \in \mathcal{V}\}$, where the vector $e$ of the L♮-convexity inequality for $g$ acts on all $n + 1$ coordinates of $(x, \xi)$.
--
--   In the backlogging model this is how the continuation value $f_{t+1}(\tilde s)$, with $\tilde s = (s_2 - a, \dots, s_l - a)$, is seen to be L♮-concave in $(s, s_l, a)$.
--
--   **Formalization Note** Real case only. The joint vector $(x, \xi)$ is `w : Option ι → ℝ` with $x = $ `w ∘ some` and $\xi = $ `w none`, over a finite index type $\iota$. The paper's statement on the whole space with value $+\infty$ off the effective domain is stated on the domain, per the paper's convention for L♮-convexity on a set.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Lemma 1, p. 287 (PDF p. 5)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_LNatConvex

namespace PerishablePricing.Backlog

/-- Lemma 1 (p. 287), on a domain. The joint vector `w : Option ι → ℝ` is `(x, ξ)`, with
`x = w ∘ some` and `ξ = w none`. If `f` is L♮-convex on `S`, then `g(x, ξ) = f(x − ξe)` is
L♮-convex on its domain `{(x, ξ) : x − ξe ∈ S}`. -/
theorem lemma_1 {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hf : LNatConvexOn S f) :
    LNatConvexOn {w : Option ι → ℝ | (fun i => w (some i) - w none) ∈ S}
      (fun w => f (fun i => w (some i) - w none)) := by sorry

end PerishablePricing.Backlog
