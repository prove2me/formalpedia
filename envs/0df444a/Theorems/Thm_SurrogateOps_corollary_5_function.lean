-- Prove2me | Theorems.Thm_SurrogateOps_corollary_5_function
-- name    : SurrogateOps.corollary_5_function
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:50:59.058935+00:00
-- url     : https://prove2.me/theorems/f4d443ba-af07-4d03-ba36-09190bb8da4d
-- title:
--   Corollary 5, p.4 — function accuracy implies uniformly bounded models
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be continuous, $x_0\in\mathbb R^d$, $\bar\Delta>0$. If the class of models $\{\tilde f_\Delta\}_{(0,\bar\Delta]}$ provides order-$N$ function accuracy of $f$ at $x_0$, then it is uniformly bounded at $x_0$. If it provides order-$N$ function accuracy of $f$ near $x_0$, then it is uniformly bounded near $x_0$.
--
--   A good approximation of a continuous function cannot blow up as $\Delta$ varies. The bound obtained is the number $M_{\tilde f}(x_0)$ used in the product theorems.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0, in the hypothesis of an implication → κ universally quantified over the implication; reason: (∀ κ, P κ → Q) is equivalent to ((∃ κ, P κ) → Q)
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Corollary 5, p.4

import Mathlib
import Definitions.Def_SurrogateOps_FunAccAt
import Definitions.Def_SurrogateOps_FunAccNear
import Definitions.Def_SurrogateOps_UnifBddAt
import Definitions.Def_SurrogateOps_UnifBddNear

namespace SurrogateOps

/-- **Corollary 5, first sentence.** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Corollary 5, p.4.
If `f ∈ C⁰` and `{f̃_Δ}` provides order-`N` function accuracy of `f` at/near `x0`, then `{f̃_Δ}` is
uniformly bounded at/near `x0`.

**Formalization Note.** `κ` is universally quantified, which is the same as an existential in the
hypothesis of each implication. -/
theorem corollary_5_function {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (Δbar N κ : ℝ)
    (hΔbar : 0 < Δbar) (hf : Continuous f) :
    (FunAccAt f fm x0 Δbar N κ → UnifBddAt fm x0 Δbar) ∧
      (FunAccNear f fm x0 Δbar N κ → UnifBddNear fm x0 Δbar) := by sorry

end SurrogateOps
