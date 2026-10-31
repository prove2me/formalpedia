-- Prove2me | Theorems.Thm_SurrogateOps_theorem_14
-- name    : SurrogateOps.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:05.830966+00:00
-- url     : https://prove2.me/theorems/0f8b6a77-8b5d-4bfa-85d5-5b166a3bfbaf
-- title:
--   Theorem 14, p.9 — function accuracy of a product of $n$ models at/near $x_0$
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ be continuous, with $F=f_1\cdots f_n$ and $\tilde F_\Delta=\tilde f_{1,\Delta}\cdots\tilde f_{n,\Delta}$. Suppose that $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_i$ function accuracy of $f_i$ at (resp. near) $x_0$ with constant $\kappa^f_i(x_0)$ for every $i$, and let $N^f_F=\min_iN^f_i$. Let $M_{f_i}(x_0)$ bound $|f_i|$ on $B_{\bar\Delta}(x_0)$ and let $M_{\tilde f_i}(x_0)$ be a uniform bound of the $i$-th class at (resp. near) $x_0$. Put
--
--   $$
--   K^f_F(x_0)=\min\Bigl\{\sum_{i=1}^n\Bigl(\prod_{j=1}^{i-1}M_{f_{\sigma(j)}}(x_0)\prod_{k=i+1}^nM_{\tilde f_{\sigma(k)}}(x_0)\Bigr)\kappa^f_{\sigma(i)}(x_0)\bar\Delta^{N^f_{\sigma(i)}-N^f_F}:\sigma\in S_n\Bigr\}.\tag{1}
--   $$
--
--   Then for every $\Delta\in(0,\bar\Delta]$:
--
--   1. if the accuracy is at $x_0$, then $|F(x_0)-\tilde F_\Delta(x_0)|\le K^f_F(x_0)\Delta^{N^f_F}$;
--   2. if the accuracy is near $x_0$, then $|F(x)-\tilde F_\Delta(x)|\le K^f_F(x_0)\Delta^{N^f_F}$ for all $x\in B_\Delta(x_0)$.
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^f_F$ function accuracy of $F$ at (resp. near) $x_0$.
--
--   The minimum over $S_n$ records that the factors may be taken in any order.
--
--   **Formalization Note** In (1), $j$ and $k$ are positions in the permuted order: `Finset.Iio i` and `Finset.Ioi i` in `Fin n`. The two cases are the two conjuncts of the conclusion.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]}, the indices {1, …, n} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar, Fin n; reason: Lean convention; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; reason: the theorems name the constant κ_i(x₀); the order clause of the conclusion is ∃ κ
--   - encoding: min of a finite family of reals → IsLeast (Set.range _) _, for the order and for (1); reason: IsLeast says exactly "is the minimum of", with no junk value
--   - reading: n is not constrained on the page → IsLeast (Set.range …) forces the index type to be nonempty, so n ≥ 1; reason: the page's minimum needs at least one index; n = 1 is included
--   - encoding: M-bounds: M_{f_i}(x₀), M_{f̃_i}(x₀) → numbers with hypotheses on |f_i| over B_Δ̄(x₀) and on the models at (case i) or near (case ii) x₀; reason: the page says "we use … to denote these bounds"; the theorem holds for every valid choice, and no sSup junk value can enter
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 14, eq. (1), p.9

import Mathlib
import Definitions.Def_SurrogateOps_FunAccAt
import Definitions.Def_SurrogateOps_FunAccNear

namespace SurrogateOps

/-- **Theorem 14 (Function accuracy at/near `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Theorem 14, eq. (1), p.9.
For `F = f₁⋯f_n`, `F̃_Δ = f̃_{1,Δ}⋯f̃_{n,Δ}` and `N_F = min{N_i}`: in case (i) (accuracy at `x0`)
`|F(x0) - F̃_Δ(x0)| ≤ K Δ^{N_F}`, in case (ii) (accuracy near `x0`) the same bound for every
`x ∈ B_Δ(x0)`, with `K` the minimum (1) over all permutations `σ ∈ S_n`; and `{F̃_Δ}` provides
order-`N_F` accuracy at/near `x0`.

**Formalization Note.** `Fin n` replaces `{1, …, n}`, and `Finset.Iio i`, `Finset.Ioi i` are the
positions before and after `i`. `IsLeast (Set.range _) _` says "is the minimum of"; it forces
`n ≥ 1`, the page's implicit range of `n`. `Mf i` bounds `|f i|` on `B_Δ̄(x0)` (p.4). `Mft i` is the
uniform bound of the `i`-th class (Corollary 5): at `x0` in case (i), near `x0` in case (ii). -/
theorem theorem_14 {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : Fin n → ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar NF K : ℝ) (N κ Mf Mft : Fin n → ℝ)
    (hΔbar : 0 < Δbar) (hf : ∀ i, Continuous (f i))
    (hMf : ∀ i, ∀ x ∈ Metric.closedBall x0 Δbar, |f i x| ≤ Mf i)
    (hNF : IsLeast (Set.range N) NF)
    (hK : IsLeast (Set.range fun σ : Equiv.Perm (Fin n) =>
      ∑ i : Fin n, ((∏ j ∈ Finset.Iio i, Mf (σ j)) * (∏ k ∈ Finset.Ioi i, Mft (σ k)))
        * κ (σ i) * Δbar ^ (N (σ i) - NF)) K) :
    ((∀ i, FunAccAt (f i) (fm i) x0 Δbar (N i) (κ i)) →
      (∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, |fm i Δ x0| ≤ Mft i) →
      (∀ Δ ∈ Set.Ioc 0 Δbar,
        |(∏ i, f i x0) - ∏ i, fm i Δ x0| ≤ K * Δ ^ NF) ∧
      ∃ κ', FunAccAt (fun x => ∏ i, f i x) (fun Δ x => ∏ i, fm i Δ x) x0 Δbar NF κ') ∧
    ((∀ i, FunAccNear (f i) (fm i) x0 Δbar (N i) (κ i)) →
      (∀ i, ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, |fm i Δ x| ≤ Mft i) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
        |(∏ i, f i x) - ∏ i, fm i Δ x| ≤ K * Δ ^ NF) ∧
      ∃ κ', FunAccNear (fun x => ∏ i, f i x) (fun Δ x => ∏ i, fm i Δ x) x0 Δbar NF κ') := by sorry

end SurrogateOps
