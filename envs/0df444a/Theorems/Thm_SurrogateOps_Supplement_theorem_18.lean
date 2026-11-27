-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_18
-- name    : SurrogateOps.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:38:51.713153+00:00
-- url     : https://prove2.me/theorems/2bf10ce2-a2f9-4a02-9918-b51652f1fabb
-- title:
--   Theorem 18, p.11 — a product of $n$ models accurate near $x_0$ has gradient accuracy of order $\min\{N^f_i,N^g_i\}$ near $x_0$
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be $C^1$, $F=f_1\cdots f_n$ and $\tilde F_\Delta=\tilde f_{1,\Delta}\cdots\tilde f_{n,\Delta}$. Suppose that for every $i$ the class $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_i$ function accuracy and order-$N^g_i$ gradient accuracy of $f_i$ near $x_0$. Then $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^{fg}_F$ gradient accuracy of $F$ near $x_0$, where
--
--   $$
--   N^{fg}_F=\min\{N^f_i,N^g_i:i=1,\dots,n\}.
--   $$
--
--   It extends Theorem 10 from two factors to $n$.
--
--   **Formalization Note** The indices are `Fin n`; the minimum is stated with `IsLeast`, which requires $n\ge1$. The models are assumed differentiable at every point of $B_\Delta(x_0)$.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]}, the indices {1, …, n} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar, Fin n; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - reading: ∇f̃_{i,Δ}(x) is used without stating the regularity of the models → DifferentiableAt ℝ (fm i Δ) x for every Δ ∈ (0, Δ̄] and every x ∈ B_Δ(x₀); reason: the page's ∇f̃_{i,Δ}(x) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: min{… : i = 1, …, n} → IsLeast (Set.range _ ∪ …) NF; reason: IsLeast says exactly "is the minimum of", with no junk value
--   - reading: n is not constrained on the page → IsLeast (Set.range …) forces the index type to be nonempty, so n ≥ 1; reason: the page's minimum needs at least one index; n = 1 is included
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 18, p.11

import Mathlib
import Definitions.Def_SurrogateOps_FunAccNear
import Definitions.Def_SurrogateOps_GradAccNear

namespace SurrogateOps.Supplement

/-- **Theorem 18 (Gradient accuracy near `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of
Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 18, p.11.
For `F = f₁⋯f_n` and `F̃_Δ = f̃_{1,Δ}⋯f̃_{n,Δ}`, if each class provides order-`N^f_i` function accuracy
and order-`N^g_i` gradient accuracy of `f_i` near `x0`, then `{F̃_Δ}` provides order-`N^{fg}_F` gradient
accuracy of `F` near `x0`, `N^{fg}_F = min{N^f_i, N^g_i : i = 1, …, n}`.

**Formalization Note.** `Fin n` replaces `{1, …, n}`; `IsLeast (Set.range Nf ∪ Set.range Ng) NF` says
`NF` is the minimum of all `N^f_i`, `N^g_i` and forces `n ≥ 1`, the page's implicit range of `n`.
`∇f̃_{i,Δ}(x)` must exist on `B_Δ(x0)`; `hm` states that. -/
theorem theorem_18 {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : Fin n → ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar NF : ℝ) (Nf Ng κf κg : Fin n → ℝ)
    (hΔbar : 0 < Δbar) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hm : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, DifferentiableAt ℝ (fm i Δ) x)
    (hfa : ∀ i, FunAccNear (f i) (fm i) x0 Δbar (Nf i) (κf i))
    (hg : ∀ i, GradAccNear (f i) (fm i) x0 Δbar (Ng i) (κg i))
    (hNF : IsLeast (Set.range Nf ∪ Set.range Ng) NF) :
    ∃ κ, GradAccNear (fun x => ∏ i, f i x) (fun Δ x => ∏ i, fm i Δ x) x0 Δbar NF κ := by sorry

end SurrogateOps.Supplement
