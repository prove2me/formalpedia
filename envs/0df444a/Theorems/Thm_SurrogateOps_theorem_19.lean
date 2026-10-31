-- Prove2me | Theorems.Thm_SurrogateOps_theorem_19
-- name    : SurrogateOps.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:50:45.353261+00:00
-- url     : https://prove2.me/theorems/0ce6f411-1db5-4dc0-8575-b2d86f65b99d
-- title:
--   Theorem 19, p.11 — a product of $n$ models exact at $x_0$ has Hessian accuracy of order $\min\{N^g_i,N^h_i\}$ at $x_0$, with constant (3)
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be $C^2$, with $F=f_1\cdots f_n$, $\tilde F_\Delta=\tilde f_{1,\Delta}\cdots\tilde f_{n,\Delta}$ and $F_i=\prod_{j\ne i}f_j$. Suppose that for every $i$ and all $\Delta\in(0,\bar\Delta]$ the model satisfies $\tilde f_{i,\Delta}(x_0)=f_i(x_0)$ (order-$\infty$ function accuracy at $x_0$ with constant $0$), and that $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^g_i$ gradient accuracy with constant $\kappa^g_i(x_0)$ and order-$N^h_i$ Hessian accuracy with constant $\kappa^h_i(x_0)$ of $f_i$ at $x_0$. Let $N^{gh}_F=\min\{N^g_i,N^h_i:i=1,\dots,n\}$. Let $M_{\nabla f_i}(x_0)$ bound $\|\nabla f_i\|$ on $B_{\bar\Delta}(x_0)$ and let $M_{\nabla\tilde f_i}(x_0)$ bound $\|\nabla\tilde f_{i,\Delta}(x_0)\|$ uniformly in $\Delta$. Then for every $\Delta\in(0,\bar\Delta]$
--
--   $$
--   \|\nabla^2F(x_0)-\nabla^2\tilde F_\Delta(x_0)\|\le K^h_F(x_0)\Delta^{N^{gh}_F},
--   $$
--
--   where
--
--   $$
--   \begin{aligned}
--   K^h_F(x_0)={}&\sum_{i=1}^n\Bigl[\sum_{j\ne i}\Bigl(\prod_{k\ne i,j}|f_k(x_0)|\Bigr)\bigl(M_{\nabla f_j}(x_0)+M_{\nabla\tilde f_j}(x_0)\bigr)\Bigr]\kappa^g_i(x_0)\bar\Delta^{N^g_i-N^{gh}_F}\\
--   &+\sum_{i=1}^n|F_i(x_0)|\,\kappa^h_i(x_0)\bar\Delta^{N^h_i-N^{gh}_F}.
--   \end{aligned}\tag{3}
--   $$
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^{gh}_F$ Hessian accuracy for $F$ at $x_0$.
--
--   This is the paper's headline error bound for products: a surrogate built by multiplying sub-models exact at $x_0$ has Hessian error of the order of the worst gradient or Hessian order among its factors, with a constant computable from the sub-models.
--
--   **Formalization Note** In (3), $j$ runs over `univ.erase i` and $k$ over `(univ.erase i).erase j`, so the pairs $(i,j)$ are ordered.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]}, the indices {1, …, n} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar, Fin n; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: the Hessian ∇²f as a matrix → fderiv ℝ (fderiv ℝ f) as a bilinear map; reason: the matrix and the second derivative determine each other; same instances
--   - reading: ‖·‖ on Hessians is unspecified → the operator norm of E →L[ℝ] E →L[ℝ] ℝ; reason: the spectral norm is the standard matrix norm in this literature and the one the proof's ‖ab^⊤‖ = ‖a‖‖b‖ uses; on a matrix it equals the operator norm of the bilinear map
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; reason: the theorems name the constant κ_i(x₀); the order clause of the conclusion is ∃ κ
--   - encoding: order-∞ function accuracy at x₀ with constant κ^f_i(x₀) = 0 → fm i Δ x0 = f i x0 for every Δ ∈ (0, Δ̄]; reason: the page states the equivalence itself (p.6)
--   - reading: ∇²f̃_{i,Δ}(x₀) is used without stating the regularity of the models → ContDiffAt ℝ 2 (fm i Δ) x0 for every Δ ∈ (0, Δ̄]; reason: the page's ∇²f̃_{i,Δ}(x₀) presupposes it; every C² model qualifies; Lean's fderiv is 0 at a non-differentiable point, where the product rule fails
--   - encoding: min of a finite family of reals → IsLeast (Set.range _) _, for the order and for (1); reason: IsLeast says exactly "is the minimum of", with no junk value
--   - reading: n is not constrained on the page → IsLeast (Set.range …) forces the index type to be nonempty, so n ≥ 1; reason: the page's minimum needs at least one index; n = 1 is included
--   - encoding: K^h_F(x₀) → the number is a variable fixed by an equation or IsLeast hypothesis; reason: same as the page's "Let" and "where"
--   - encoding: M-bounds: M_{∇f_i}(x₀), M_{∇f̃_i}(x₀) → numbers with hypotheses on ‖∇f_i‖ over B_Δ̄(x₀) and on ‖∇f̃_{i,Δ}(x₀)‖ for Δ ∈ (0, Δ̄]; reason: the page says "we use … to denote these bounds"; the theorem holds for every valid choice, and no sSup junk value can enter
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 19, eq. (3), p.11

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt
import Definitions.Def_SurrogateOps_HessAccAt

namespace SurrogateOps

/-- **Theorem 19 (Hessian accuracy at `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Theorem 19, eq. (3), p.11.
For `F = f₁⋯f_n`, `F̃_Δ = f̃_{1,Δ}⋯f̃_{n,Δ}`, models exact at `x0` and `N = min{N^g_i, N^h_i}`:
`‖∇²F(x0) - ∇²F̃_Δ(x0)‖ ≤ K Δ^N` with `K` the constant (3), and `{F̃_Δ}` provides order-`N` Hessian
accuracy of `F` at `x0`.

**Formalization Note.** `Fin n` replaces `{1, …, n}`; `IsLeast (Set.range Ng ∪ Set.range Nh) NF` says
`NF` is the minimum of all `N^g_i`, `N^h_i` and forces `n ≥ 1`, the page's implicit range of `n`.
Order-∞ function accuracy at `x0` with constant `0` is the equality `fm i Δ x0 = f i x0` (p.6).
`∇²f̃_{i,Δ}(x0)` must exist for the page's statement to make sense; `hm` states that (`ContDiffAt`:
every `C²` model qualifies). `Mg i` bounds `‖∇f_i‖` on `B_Δ̄(x0)` (p.4). `Mgt i` is the uniform bound
of `‖∇f̃_{i,Δ}(x0)‖` (Corollary 5). They are hypotheses rather than `sSup`s, so the theorem holds for
every valid choice. In (3), `j` runs over `univ.erase i` and `k` over `(univ.erase i).erase j`, so the
pairs `(i, j)` are ordered. -/
theorem theorem_19 {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : Fin n → ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar NF K : ℝ) (Ng Nh κg κh Mg Mgt : Fin n → ℝ)
    (hΔbar : 0 < Δbar) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hm : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, ContDiffAt ℝ 2 (fm i Δ) x0)
    (he : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, fm i Δ x0 = f i x0)
    (hg : ∀ i, GradAccAt (f i) (fm i) x0 Δbar (Ng i) (κg i))
    (hh : ∀ i, HessAccAt (f i) (fm i) x0 Δbar (Nh i) (κh i))
    (hMg : ∀ i, ∀ x ∈ Metric.closedBall x0 Δbar, ‖fderiv ℝ (f i) x‖ ≤ Mg i)
    (hMgt : ∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, ‖fderiv ℝ (fm i Δ) x0‖ ≤ Mgt i)
    (hNF : IsLeast (Set.range Ng ∪ Set.range Nh) NF)
    (hK : K =
      ∑ i : Fin n,
        (∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j, |f k x0|) * (Mg j + Mgt j))
          * κg i * Δbar ^ (Ng i - NF)
      + ∑ i : Fin n,
        |∏ j ∈ Finset.univ.erase i, f j x0| * κh i * Δbar ^ (Nh i - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fderiv ℝ (fun x => ∏ i, f i x)) x0
          - fderiv ℝ (fderiv ℝ (fun x => ∏ i, fm i Δ x)) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, HessAccAt (fun x => ∏ i, f i x) (fun Δ x => ∏ i, fm i Δ x) x0 Δbar NF κ := by sorry

end SurrogateOps
