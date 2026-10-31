-- Prove2me | Theorems.Thm_SurrogateOps_theorem_16
-- name    : SurrogateOps.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:50:44.789069+00:00
-- url     : https://prove2.me/theorems/b5194520-0bb5-4108-a219-4e16419ea56d
-- title:
--   Theorem 16, p.10 — gradient accuracy of a product of $n$ models exact at $x_0$
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be $C^1$, with $F=f_1\cdots f_n$ and $\tilde F_\Delta=\tilde f_{1,\Delta}\cdots\tilde f_{n,\Delta}$. Suppose that for every $i$ and all $\Delta\in(0,\bar\Delta]$ the model satisfies $\tilde f_{i,\Delta}(x_0)=f_i(x_0)$, and that $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^g_i$ gradient accuracy of $f_i$ at $x_0$ with constant $\kappa^g_i(x_0)$. Let $N^g_F=\min_iN^g_i$. Then for every $\Delta\in(0,\bar\Delta]$
--
--   $$
--   \|\nabla F(x_0)-\nabla\tilde F_\Delta(x_0)\|\le K^g_F\Delta^{N^g_F},
--   \qquad
--   K^g_F=\sum_{i=1}^n\Bigl(\prod_{j\ne i}|f_j(x_0)|\Bigr)\kappa^g_i(x_0)\bar\Delta^{N^g_i-N^g_F}.\tag{2}
--   $$
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^g_F$ gradient accuracy of $F$ at $x_0$.
--
--   This is the $n$-factor form of Theorem 8.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]}, the indices {1, …, n} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar, Fin n; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; reason: the theorems name the constant κ_i(x₀); the order clause of the conclusion is ∃ κ
--   - encoding: order-∞ function accuracy at x₀ with constant κ^f_i(x₀) = 0 → fm i Δ x0 = f i x0 for every Δ ∈ (0, Δ̄]; reason: the page states the equivalence itself (p.6)
--   - reading: ∇f̃_{i,Δ}(x₀) is used without stating that the models are differentiable → DifferentiableAt ℝ (fm i Δ) x0 for every Δ ∈ (0, Δ̄]; reason: the page's ∇f̃_{i,Δ}(x₀) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product rule fails
--   - encoding: min of a finite family of reals → IsLeast (Set.range _) _, for the order and for (1); reason: IsLeast says exactly "is the minimum of", with no junk value
--   - reading: n is not constrained on the page → IsLeast (Set.range …) forces the index type to be nonempty, so n ≥ 1; reason: the page's minimum needs at least one index; n = 1 is included
--   - encoding: K^g_F → the number is a variable fixed by an equation or IsLeast hypothesis; reason: same as the page's "Let" and "where"
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 16, eq. (2), p.10

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt

namespace SurrogateOps

/-- **Theorem 16 (Gradient accuracy at `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Theorem 16, eq. (2), p.10.
For `F = f₁⋯f_n`, `F̃_Δ = f̃_{1,Δ}⋯f̃_{n,Δ}`, models exact at `x0` and `N_F = min{N_i}`:
`‖∇F(x0) - ∇F̃_Δ(x0)‖ ≤ K Δ^{N_F}` with `K` the constant (2), and `{F̃_Δ}` provides order-`N_F`
gradient accuracy of `F` at `x0`.

**Formalization Note.** `Fin n` replaces `{1, …, n}`; `IsLeast (Set.range N) NF` says `NF` is the
minimum of the `N i` and forces `n ≥ 1`, the page's implicit range of `n`. Order-∞ function accuracy
at `x0` with constant `0` is the equality `fm i Δ x0 = f i x0` (p.6). `∇f̃_{i,Δ}(x0)` must exist for
the page's statement to make sense; `hm` states that. -/
theorem theorem_16 {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : Fin n → ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar NF K : ℝ) (N κ : Fin n → ℝ)
    (hΔbar : 0 < Δbar) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (hm : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, DifferentiableAt ℝ (fm i Δ) x0)
    (he : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, fm i Δ x0 = f i x0)
    (hg : ∀ i, GradAccAt (f i) (fm i) x0 Δbar (N i) (κ i))
    (hNF : IsLeast (Set.range N) NF)
    (hK : K = ∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, |f j x0|) * κ i * Δbar ^ (N i - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fun x => ∏ i, f i x) x0 - fderiv ℝ (fun x => ∏ i, fm i Δ x) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ', GradAccAt (fun x => ∏ i, f i x) (fun Δ x => ∏ i, fm i Δ x) x0 Δbar NF κ' := by sorry

end SurrogateOps
