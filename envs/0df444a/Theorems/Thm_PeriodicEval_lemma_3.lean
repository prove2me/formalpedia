-- Prove2me | Theorems.Thm_PeriodicEval_lemma_3
-- name    : PeriodicEval.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:02.030091+00:00
-- url     : https://prove2.me/theorems/f2441463-377d-4658-8300-37b88fd7f58a
-- title:
--   Lemma 3 — bounds on $\Phi$ and on the fixed point $A^*$
-- statement:
--   Under the standing assumptions, with $a^+=\max(a,0)$:
--
--   1. for all $a\in\mathbb R$,
--   $$\max\big(e^{-\beta\tau}U(e^{r\tau}-\gamma)+ae^{-(\beta-\alpha r)\tau},\,-k\gamma^\alpha e^{-\beta\tau}\big)\le\Phi(a)\le e^{-(\beta-h)\tau}(a^++1);$$
--   2. the fixed point $A^*$ of $\Phi$ satisfies
--   $$\frac{e^{-\beta\tau}U(e^{r\tau}-\gamma)}{1-e^{-(\beta-r\alpha)\tau}}\le A^*\le\frac{e^{-(\beta-h)\tau}}{1-e^{-(\beta-h)\tau}};$$
--   3. $A^*\le0$ if and only if $\Phi(0)\le0$.
--
--   Part 1 gives $A^*\ge0$ when $k=0$; part 2 excludes Case 4 of Proposition 3 at the fixed point.
--
--   **Formalization Note** $\Phi$ is extended-real valued and the bounds are compared in the extended reals. Both denominators are positive because $\beta-r\alpha\ge\beta-h>0$.
--
--   Differences from the source:
--   - encoding: A* the unique fixed point of Φ → every real A with Φ(A) = A; reason: there is exactly one (Proposition 4), so the instances are the same
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), Lemma 3, pp.40–41

import Mathlib
import Definitions.Def_PeriodicEval_Auxiliary

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace PeriodicEval

/-- Lemma 3, SSRN 3971852 (June 20, 2023), pp.40–41, bounds on `Φ` (24) and on its fixed point:
1. for all `a ∈ ℝ`,
   `max(e^{−βτ}U(e^{rτ} − γ) + a e^{−(β−αr)τ}, −kγ^α e^{−βτ}) ≤ Φ(a) ≤ e^{−(β−h)τ}(a⁺ + 1)`;
2. the fixed point `A*` of `Φ` satisfies
   `e^{−βτ}U(e^{rτ} − γ)/(1 − e^{−(β−rα)τ}) ≤ A* ≤ e^{−(β−h)τ}/(1 − e^{−(β−h)τ})`;
3. `A* ≤ 0` if and only if `Φ(0) ≤ 0`.

**Formalization Note** `Φ` is `EReal`-valued and the bounds are compared in `EReal`. "A* the
unique fixed point" is a real `A` with `Φ(A) = A` (unique by Proposition 4). Both
denominators are positive: `β − rα ≥ β − h > 0`. -/
theorem lemma_3 (p : Params) (hp : p.Standing) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (ℱ : Filtration ℝ≥0 m) (hℱ : IsAugmentedNaturalFiltration P B ℱ) :
    (∀ a : ℝ,
      ((max (Real.exp (-(p.β * p.τ)) * U p (Real.exp (p.r * p.τ) - p.γ) +
              a * Real.exp (-((p.β - p.α * p.r) * p.τ)))
            (-(p.k * p.γ ^ p.α * Real.exp (-(p.β * p.τ)))) : ℝ) : EReal) ≤ Φ p P ℱ B a ∧
      Φ p P ℱ B a ≤ ((Real.exp (-((p.β - p.h) * p.τ)) * (max a 0 + 1) : ℝ) : EReal)) ∧
    (∀ A : ℝ, Φ p P ℱ B A = (A : EReal) →
      Real.exp (-(p.β * p.τ)) * U p (Real.exp (p.r * p.τ) - p.γ) /
          (1 - Real.exp (-((p.β - p.r * p.α) * p.τ))) ≤ A ∧
        A ≤ Real.exp (-((p.β - p.h) * p.τ)) / (1 - Real.exp (-((p.β - p.h) * p.τ)))) ∧
    (∀ A : ℝ, Φ p P ℱ B A = (A : EReal) → (A ≤ 0 ↔ Φ p P ℱ B 0 ≤ 0)) := by sorry

end PeriodicEval
