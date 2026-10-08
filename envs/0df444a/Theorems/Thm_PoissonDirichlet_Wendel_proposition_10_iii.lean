-- Prove2me | Theorems.Thm_PoissonDirichlet_Wendel_proposition_10_iii
-- name    : PoissonDirichlet.Wendel.proposition_10_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:39.479551+00:00
-- url     : https://prove2.me/theorems/91d4ffa8-d81b-46b4-95f7-e420f3908b09
-- title:
--   Proposition 10 (iii), p. 862 — X_n = L V_n^{−α} are the arrival times of a unit Poisson process, and (29)
-- statement:
--   Let $0<\alpha<1$ and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ distribution. Let $L$ be the almost-sure limit $L=\lim_{n\to\infty}nV_n^\alpha$ of (24), and put $X_n=LV_n^{-\alpha}$ as in (27). Then:
--
--   1. (28) the sequence $(X_1,X_2,\dots)$ has the same law as $(\varepsilon_1,\ \varepsilon_1+\varepsilon_2,\ \varepsilon_1+\varepsilon_2+\varepsilon_3,\dots)$ for independent standard exponential variables $\varepsilon_i$, i.e. the $X_n$ are the points of a unit-rate Poisson process on $(0,\infty)$;
--   2. (29) almost surely, for every $n$,
--   $$V_n=\frac{X_n^{-1/\alpha}}{\sum_m X_m^{-1/\alpha}}.$$
--
--   This is the bridge from the PD$(\alpha,0)$ sequence to Poisson arrival times on which the computations of the paper rest.
--
--   **Formalization Note** $L$ is a given random variable together with the hypothesis that $nV_n^\alpha\to L$ almost surely: this is the definition (24), not an extra assumption (its existence is Proposition 10 (i)). The equality of laws in (28) is stated as: there is a probability measure on sequences under which the coordinates are i.i.d. standard exponential and which gives every measurable set of sequences, pulled back through the partial-sum map, the same mass as the law of $(X_n)$. The constant $C$ of (27) does not appear, since $X_n=LV_n^{-\alpha}$ does not depend on it. 0-based indexing: `V ω k` is $V_{k+1}$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 862, Proposition 10 (iii), (24), (27)–(29)

import Mathlib
import Definitions.Def_PoissonDirichlet_Wendel_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Wendel

/-- Proposition 10 (iii), p. 862: for `V` with law PD(α, 0), 0 < α < 1, and the local time
`L = lim n V_n^α` (24), the variables `X_n = L V_n^{-α}` (27) are distributed as the partial
sums `ε_1 + ⋯ + ε_n` of i.i.d. standard exponentials (28), and (29)
`V_n = X_n^{-1/α} / Σ_m X_m^{-1/α}` holds a.s. 0-based: `V ω k` is `V_{k+1}`. -/
theorem proposition_10_iii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω))) :
    (∃ μ : Measure (ℕ → ℝ), IsProbabilityMeasure μ ∧
        iIndepFun (fun i (e : ℕ → ℝ) => e i) μ ∧
        (∀ i : ℕ, HasLaw (fun e : ℕ → ℝ => e i) (expMeasure 1) μ) ∧
        ∀ s : Set (ℕ → ℝ), MeasurableSet s →
          P ((fun ω k => L ω * V ω k ^ (-α)) ⁻¹' s) =
            μ ((fun (e : ℕ → ℝ) (k : ℕ) => ∑ i ∈ Finset.range (k + 1), e i) ⁻¹' s)) ∧
    (∀ᵐ ω ∂P, ∀ k : ℕ, V ω k =
        (L ω * V ω k ^ (-α)) ^ (-1 / α) / ∑' m : ℕ, (L ω * V ω m ^ (-α)) ^ (-1 / α)) := by sorry

end PoissonDirichlet.Wendel
