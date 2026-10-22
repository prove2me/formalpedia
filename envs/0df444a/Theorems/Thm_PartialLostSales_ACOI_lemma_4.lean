-- Prove2me | Theorems.Thm_PartialLostSales_ACOI_lemma_4
-- name    : PartialLostSales.ACOI.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:55.039518+00:00
-- url     : https://prove2.me/theorems/2b283efa-ed78-4f17-aaa6-1bf23651a6d9
-- title:
--   Lemma 4, p. 14 — coupled lost-sales processes: V^ζ_α(x) − V^ζ_α(x′) ≤ h⁻(x′−x) − I{x′−x ≥ C}h′(x′−x) ≤ h⁻C
-- statement:
--   Fix the lost-sales model under its standing assumptions. Consider two inventory processes $x_t$ and $x'_t$ with initial levels $x'\ge x\ge0$. They are driven by the same i.i.d. demands $D_t\sim D$ and the same order amounts $\zeta_t\in[0,K]$, given by an arbitrary **control rule** $\zeta$, which may depend on the past or even the future. The dynamics are $x_{t+1}=(x_t+\zeta_t-D_t)^+$. Let $V^\zeta_\alpha(x)$ be the expected total discounted cost, holding plus lost-sales penalty, of the process started at $x$.
--
--   Then there are constants $C>0$, $\alpha_*\in(0,1)$ and $h'>h^-$ such that, uniformly in $\alpha\in[\alpha_*,1)$, in $x'\ge x\ge0$ and in all control rules $\zeta$,
--   $$V^\zeta_\alpha(x)-V^\zeta_\alpha(x')\ \le\ h^-(x'-x)-\mathbf 1\{x'-x\ge C\}\,h'(x'-x)\ \le\ \bar C:=h^-C<\infty,$$
--   as long as $V^\zeta_\alpha(x')<\infty$.
--
--   So a lower starting inventory can save at most $h^-$ per unit of the gap in discounted cost. When the gap is at least $C$ it is in fact worse by a margin, since the extra holding cost of the higher process outweighs the lost sales it avoids. Lemma 4 is the key estimate in the proof of display (12).
--
--   **Formalization Note.** The constants are chosen before $\alpha$, the initial levels, the probability space, the demands and the control rule; they depend only on the model. The first inequality is stated in the rearranged form
--   $$V^\zeta_\alpha(x)+\mathbf 1\{x'-x\ge C\}h'(x'-x)\le V^\zeta_\alpha(x')+h^-(x'-x)$$
--   in $[0,\infty]$, which is equivalent to it because $V^\zeta_\alpha(x')<\infty$.
--
--   Demands are measurable, mutually independent and distributed as $D$. Measurability of each order amount $\zeta_t$ is **added**, so that the expectation is defined. Adaptedness is not required. Costs are realized period costs, discounted by $\alpha^t$ from period $0$. Probability spaces range over `Type`.
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, p. 14, Lemma 4, display (13)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

namespace PartialLostSales.ACOI

/-- Lemma 4, p. 14: there are constants `C > 0`, `α* ∈ (0, 1)` and `h' > h⁻` such that, uniformly
in `α ∈ [α*, 1)`, in initial inventory levels `x' ≥ x ≥ 0` and in all control rules `ζ` (order
amounts in `[0, K]`, possibly anticipating), the two inventory processes started at `x` and `x'`
and driven by the same i.i.d. demands and the same orders satisfy
`V^ζ_α(x) − V^ζ_α(x') ≤ h⁻(x' − x) − 𝟙{x' − x ≥ C} h'(x' − x) ≤ h⁻ C` whenever `V^ζ_α(x') < ∞`.
The first inequality is stated in the rearranged form
`V^ζ_α(x) + 𝟙{x' − x ≥ C} h'(x' − x) ≤ V^ζ_α(x') + h⁻(x' − x)`. -/
theorem lemma_4 (P : Params) (hP : Standing P) :
    ∃ C : ℝ, 0 < C ∧ ∃ αstar ∈ Set.Ioo (0 : ℝ) 1, ∃ h' : ℝ, P.hminus < h' ∧
      ∀ α ∈ Set.Ico αstar 1, ∀ x x' : ℝ, 0 ≤ x → x ≤ x' →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ D ζ : ℕ → Ω → ℝ,
        (∀ t, Measurable (D t)) → iIndepFun D μ → (∀ t, μ.map (D t) = P.demand) →
        (∀ t, Measurable (ζ t)) → (∀ t ω, ζ t ω ∈ Set.Icc (0 : ℝ) P.K) →
        Vζ P μ α x' ζ D ≠ ⊤ →
        Vζ P μ α x ζ D + ENNReal.ofReal (if C ≤ x' - x then h' * (x' - x) else 0) ≤
            Vζ P μ α x' ζ D + ENNReal.ofReal (P.hminus * (x' - x)) ∧
          P.hminus * (x' - x) - (if C ≤ x' - x then h' * (x' - x) else 0) ≤
            P.hminus * C := by sorry

end PartialLostSales.ACOI
