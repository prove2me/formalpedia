-- Prove2me | Theorems.Thm_SurrogateOps_theorem_6
-- name    : SurrogateOps.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:03.213836+00:00
-- url     : https://prove2.me/theorems/c5303a5f-17a7-4ff7-887b-1cffce9e5544
-- title:
--   Theorem 6, p.5 — function accuracy of a product of two models at/near $x_0$
-- statement:
--   Let $f_1,f_2:\mathbb R^d\to\mathbb R$ be continuous, with $F=f_1f_2$ and $\tilde F_\Delta=\tilde f_{1,\Delta}\tilde f_{2,\Delta}$. Suppose that $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_i$ function accuracy of $f_i$ at (resp. near) $x_0$ with constant $\kappa^f_i(x_0)$, for $i=1,2$, and let $N^f_F=\min\{N^f_1,N^f_2\}$. Let $M_{f_i}(x_0)$ bound $|f_i|$ on $B_{\bar\Delta}(x_0)$ and let $M_{\tilde f_i}(x_0)$ be a uniform bound of the $i$-th class at (resp. near) $x_0$. Put
--
--   $$
--   K^f_F(x_0)=\min\bigl\{M_{\tilde f_2}\kappa^f_1\bar\Delta^{N^f_1-N^f_F}+M_{f_1}\kappa^f_2\bar\Delta^{N^f_2-N^f_F},\ M_{f_2}\kappa^f_1\bar\Delta^{N^f_1-N^f_F}+M_{\tilde f_1}\kappa^f_2\bar\Delta^{N^f_2-N^f_F}\bigr\}.
--   $$
--
--   Then for every $\Delta\in(0,\bar\Delta]$:
--
--   1. if the accuracy is at $x_0$, then $|F(x_0)-\tilde F_\Delta(x_0)|\le K^f_F(x_0)\Delta^{N^f_F}$;
--   2. if the accuracy is near $x_0$, then $|F(x)-\tilde F_\Delta(x)|\le K^f_F(x_0)\Delta^{N^f_F}$ for all $x\in B_\Delta(x_0)$.
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^f_F$ function accuracy of $F$ at (resp. near) $x_0$.
--
--   A product of two models is as accurate as its worse factor, with an explicit constant.
--
--   **Formalization Note** The two cases are the two conjuncts of the conclusion, each an implication from its own accuracy and uniform-bound hypotheses. The same variables $M_{\tilde f_i}$ serve both.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; reason: the theorems name the constant κ_i(x₀); the order clause of the conclusion is ∃ κ
--   - encoding: N^f_F and K^f_F(x₀) → the number is a variable fixed by an equation or IsLeast hypothesis; reason: same as the page's "Let" and "where"
--   - encoding: M-bounds: M_{f_i}(x₀), M_{f̃_i}(x₀) → numbers with hypotheses on |f_i| over B_Δ̄(x₀) and on the models at (case i) or near (case ii) x₀; reason: the page says "we use … to denote these bounds"; the theorem holds for every valid choice, and no sSup junk value can enter
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 6, p.5

import Mathlib
import Definitions.Def_SurrogateOps_FunAccAt
import Definitions.Def_SurrogateOps_FunAccNear

namespace SurrogateOps

/-- **Theorem 6 (Function accuracy at/near `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Theorem 6, p.5.
For `F = f₁f₂`, `F̃_Δ = f̃_{1,Δ}f̃_{2,Δ}` and `N_F = min{N₁, N₂}`: in case (i) (accuracy at `x0`)
`|F(x0) - F̃_Δ(x0)| ≤ K Δ^{N_F}`, in case (ii) (accuracy near `x0`) the same bound for every
`x ∈ B_Δ(x0)`, with `K` the constant of the page; and `{F̃_Δ}` provides order-`N_F` accuracy at/near `x0`.

**Formalization Note.** `Mf₁`, `Mf₂` bound `|f₁|`, `|f₂|` on `B_Δ̄(x0)` (p.4). `Mft₁`, `Mft₂` are the
uniform bounds of the models (Corollary 5): at `x0` in case (i), near `x0` in case (ii). They are
hypotheses rather than `sSup`s, so the theorem holds for every valid choice. `NF` and `K` are named by
the equations `hNF`, `hK`, as in the page's "Let" and "where". -/
theorem theorem_6 {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar N₁ N₂ κ₁ κ₂ Mf₁ Mf₂ Mft₁ Mft₂ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hMf₁ : ∀ x ∈ Metric.closedBall x0 Δbar, |f₁ x| ≤ Mf₁)
    (hMf₂ : ∀ x ∈ Metric.closedBall x0 Δbar, |f₂ x| ≤ Mf₂)
    (hNF : NF = min N₁ N₂)
    (hK : K = min
      (Mft₂ * κ₁ * Δbar ^ (N₁ - NF) + Mf₁ * κ₂ * Δbar ^ (N₂ - NF))
      (Mf₂ * κ₁ * Δbar ^ (N₁ - NF) + Mft₁ * κ₂ * Δbar ^ (N₂ - NF))) :
    (FunAccAt f₁ fm₁ x0 Δbar N₁ κ₁ → FunAccAt f₂ fm₂ x0 Δbar N₂ κ₂ →
      (∀ Δ ∈ Set.Ioc 0 Δbar, |fm₁ Δ x0| ≤ Mft₁) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, |fm₂ Δ x0| ≤ Mft₂) →
      (∀ Δ ∈ Set.Ioc 0 Δbar,
        |f₁ x0 * f₂ x0 - fm₁ Δ x0 * fm₂ Δ x0| ≤ K * Δ ^ NF) ∧
      ∃ κ, FunAccAt (fun x => f₁ x * f₂ x) (fun Δ x => fm₁ Δ x * fm₂ Δ x) x0 Δbar NF κ) ∧
    (FunAccNear f₁ fm₁ x0 Δbar N₁ κ₁ → FunAccNear f₂ fm₂ x0 Δbar N₂ κ₂ →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, |fm₁ Δ x| ≤ Mft₁) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, |fm₂ Δ x| ≤ Mft₂) →
      (∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ,
        |f₁ x * f₂ x - fm₁ Δ x * fm₂ Δ x| ≤ K * Δ ^ NF) ∧
      ∃ κ, FunAccNear (fun x => f₁ x * f₂ x) (fun Δ x => fm₁ Δ x * fm₂ Δ x) x0 Δbar NF κ) := by sorry

end SurrogateOps
