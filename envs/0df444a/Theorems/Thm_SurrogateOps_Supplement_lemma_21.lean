-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_lemma_21
-- name    : SurrogateOps.Supplement.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:39:55.596783+00:00
-- url     : https://prove2.me/theorems/018b8e57-e98b-4cf9-9294-f6ad80f1b7f9
-- title:
--   Lemma 21, p.13 — for $\bar\Delta$ small, the reciprocals $1/\tilde f_{2,\Delta}$ are uniformly bounded at/near $x_0$ by $M_{1/f_2}/(1-\bar\Delta^{N^f_2}M_{1/f_2}\kappa^f_2)$
-- statement:
--   Throughout §4, $f_2(x)\neq0$ and $\tilde f_{2,\Delta}(x)\neq0$ for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$, and $M_{1/f_2}(x_0)$ bounds $|1/f_2|$ on $B_{\bar\Delta}(x_0)$.
--
--   Let $f_2:\mathbb R^d\to\mathbb R$ be continuous and suppose $\{\tilde f_{2,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_2$ function accuracy of $f_2$ at (resp. near) $x_0$ with constant $\kappa^f_2(x_0)$, where $N^f_2>0$. Then:
--
--   1. some $\Delta_0\in(0,\bar\Delta]$ satisfies $1-\Delta_0^{N^f_2}M_{1/f_2}(x_0)\kappa^f_2(x_0)>0$;
--   2. for every such $\Delta_0$ and every $\Delta\in(0,\Delta_0]$,
--   $$
--   \Bigl|\frac1{\tilde f_{2,\Delta}(x)}\Bigr|\le\tilde M_{1/\tilde f_2}(x_0)=\frac{M_{1/f_2}(x_0)}{1-\Delta_0^{N^f_2}M_{1/f_2}(x_0)\kappa^f_2(x_0)}
--   $$
--   at $x=x_0$ (resp. for all $x\in B_\Delta(x_0)$).
--
--   That is, after shrinking $\bar\Delta$ to $\Delta_0$, the class $\{1/\tilde f_{2,\Delta}\}_{(0,\Delta_0]}$ is uniformly bounded at (resp. near) $x_0$ by $\tilde M_{1/\tilde f_2}(x_0)$. This bound is what makes the quotient error estimates of §4 finite.
--
--   **Formalization Note** The page's "we can choose a sufficiently small $\bar\Delta$" is items 1 and 2, with $\Delta_0$ for the chosen $\bar\Delta$ and the inequality imposed by the proof. Item 1 does not need the accuracy hypothesis.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: standing assumption of §4 (p.12): f₂(x) ≠ 0 and f̃_{2,Δ}(x) ≠ 0 for all Δ ∈ (0, Δ̄] and x ∈ B_Δ(x₀) → the hypothesis hne; reason: copied from the section's standing assumption; it is needed in Lean, where x / 0 = 0
--   - encoding: M_{1/f₂}(x₀), the bound of |1/f₂| on B_Δ̄(x₀) (p.12) → a number M with |1 / f₂ x| ≤ M for all x ∈ closedBall x0 Δbar; reason: the page names the bound without fixing it; a continuous f₂ without zeros on the compact ball always has one
--   - reading: "we can choose a sufficiently small Δ̄ such that {1/f̃_{2,Δ}}_{(0,Δ̄]} is uniformly bounded at/near x₀ by M̃_{1/f̃₂}(x₀)", with M̃ written in terms of Δ̄ → (a) some Δ₀ ∈ (0, Δ̄] has Δ₀^{N^f_2} M κ^f_2 < 1, and (b) for every such Δ₀ and every Δ ∈ (0, Δ₀], |1/f̃_{2,Δ}| ≤ M/(1 − Δ₀^{N^f_2} M κ^f_2) at x₀ (resp. on B_Δ(x₀)); reason: the proof (p.13) fixes "sufficiently small" as 1 − Δ̄^{N^f_2} M_{1/f₂}(x₀) κ^f_2(x₀) > 0; (b) for every admissible Δ₀ is stronger than for one, (a) keeps every instance of the source, and the explicit bound is the stated uniform bound
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Lemma 21 and its proof, p.13; standing assumptions of §4 and M_{1/f2}, p.12

import Mathlib
import Definitions.Def_SurrogateOps_FunAccAt
import Definitions.Def_SurrogateOps_FunAccNear

namespace SurrogateOps.Supplement

/-- **Lemma 21.** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through
Operations on Sub-models, arXiv:2112.08411v1, Lemma 21 and its proof, p.13 (standing assumptions of §4
and the bound `M_{1/f₂}(x0)`, p.12).
If `f₂ ∈ C⁰`, `{f̃_{2,Δ}}` provides order-`N^f_2` function accuracy of `f₂` at/near `x0` with constant
`κ^f_2(x0)` and `N^f_2 > 0`, then (a) a `Δ₀ ∈ (0, Δ̄]` with `1 - Δ₀^{N^f_2} M_{1/f₂}(x0) κ^f_2(x0) > 0`
exists, and (b) for every such `Δ₀` the class `{1/f̃_{2,Δ}}_{(0,Δ₀]}` is uniformly bounded at/near `x0`
by `M̃_{1/f̃₂}(x0) = M_{1/f₂}(x0) / (1 - Δ₀^{N^f_2} M_{1/f₂}(x0) κ^f_2(x0))`.

**Formalization Note.** The page's "we can choose a sufficiently small `Δ̄`" is (a) together with (b),
where `Δ₀` is the chosen `Δ̄`; the inequality is the one the proof imposes. `hne` is the standing
assumption of §4 (`f₂(x) ≠ 0`, `f̃_{2,Δ}(x) ≠ 0` on `B_Δ(x0)`), and `M` is `M_{1/f₂}(x0)`, a bound of
`|1/f₂|` on `B_Δ̄(x0)` (p.12), stated as a hypothesis. -/
theorem lemma_21 {d : ℕ} (f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar N₂ κ₂ M : ℝ)
    (hΔbar : 0 < Δbar) (hf₂ : Continuous f₂)
    (hne : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, f₂ x ≠ 0 ∧ fm₂ Δ x ≠ 0)
    (hM : ∀ x ∈ Metric.closedBall x0 Δbar, |1 / f₂ x| ≤ M)
    (hN₂ : 0 < N₂) :
    (∃ Δ₀ ∈ Set.Ioc 0 Δbar, Δ₀ ^ N₂ * M * κ₂ < 1) ∧
    (FunAccAt f₂ fm₂ x0 Δbar N₂ κ₂ →
      ∀ Δ₀ ∈ Set.Ioc 0 Δbar, Δ₀ ^ N₂ * M * κ₂ < 1 →
        ∀ Δ ∈ Set.Ioc 0 Δ₀, |1 / fm₂ Δ x0| ≤ M / (1 - Δ₀ ^ N₂ * M * κ₂)) ∧
    (FunAccNear f₂ fm₂ x0 Δbar N₂ κ₂ →
      ∀ Δ₀ ∈ Set.Ioc 0 Δbar, Δ₀ ^ N₂ * M * κ₂ < 1 →
        ∀ Δ ∈ Set.Ioc 0 Δ₀, ∀ x ∈ Metric.closedBall x0 Δ,
          |1 / fm₂ Δ x| ≤ M / (1 - Δ₀ ^ N₂ * M * κ₂)) := by sorry

end SurrogateOps.Supplement
