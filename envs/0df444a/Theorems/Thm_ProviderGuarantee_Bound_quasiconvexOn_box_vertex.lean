-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_quasiconvexOn_box_vertex
-- name    : ProviderGuarantee.Bound.quasiconvexOn_box_vertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:06.392222+00:00
-- url     : https://prove2.me/theorems/d0f36358-8fa6-455a-935f-9de30603c5b5
-- title:
--   Proof of Theorem 1, p. 39 — a quasiconvex function on a box is dominated at each point by its value at some vertex
-- statement:
--   Let $a, b \in \mathbb R^n$ and let $f : \mathbb R^n \to \mathbb R$ be quasiconvex on the box $[a, b] = \{x : a_i \le x_i \le b_i \text{ for all } i\}$. Then for every $x \in [a, b]$ there is a vertex $y$ of the box, i.e. a point with $y_i \in \{a_i, b_i\}$ for every $i$, such that
--
--   $$f(x) \le f(y).$$
--
--   Consequently, to find $\max_{\gamma \in [\gamma_{\min}, \gamma_{\max}]^n} f(\gamma)$ one need only look at the extreme points of the hypercube. The page cites Bertsekas et al. (2003) for this fact and applies it to the dual value $f$ with $a = (\gamma_{\min}, \dots, \gamma_{\min})$ and $b = (\gamma_{\max}, \dots, \gamma_{\max})$.
--
--   Differences from the source:
--   - generalization: the hypercube [γmin, γmax]^n and the function f → any box [a, b] ⊆ ℝ^n and any function quasiconvex on it; reason: the page invokes a general fact (cited to Bertsekas et al. 2003); taking a = γmin·1, b = γmax·1 and f = dualValue gives the page's use
--   - reading: 'we need only to look at the extreme points of the hypercube' → every point of the box is dominated in value by some vertex; reason: this is the precise content of the reduction: the maximum over the box equals the maximum over the vertices
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), p. 39, proof of Theorem 1 (citing Bertsekas, Nedić and Ozdaglar 2003)

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem quasiconvexOn_box_vertex {n : ℕ} (a b : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : QuasiconvexOn ℝ (Set.Icc a b) f) :
    ∀ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc a b, (∀ i, y i = a i ∨ y i = b i) ∧ f x ≤ f y := by sorry

end ProviderGuarantee.Bound
