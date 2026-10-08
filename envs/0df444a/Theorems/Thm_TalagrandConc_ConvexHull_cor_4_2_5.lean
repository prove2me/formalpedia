-- Prove2me | Theorems.Thm_TalagrandConc_ConvexHull_cor_4_2_5
-- name    : TalagrandConc.ConvexHull.cor_4_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:23.989975+00:00
-- url     : https://prove2.me/theorems/06fc862a-5d13-42c0-b788-51c703a20f83
-- title:
--   Corollary 4.2.5 — $P(A_t^c)\ge1-\exp\big(-\frac12\big(t-\sqrt{2\log(1/P(A))}\big)^2\big)$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $P=\mu^{\otimes N}$ on $\Omega^N$. For each subset $A$ of $\Omega^N$ with $P(A)>0$ and each real $t$,
--   $$t\ge\sqrt{2\log\frac{1}{P(A)}}\ \Longrightarrow\ P(A_t^c)\ge1-\exp\Big(-\frac12\Big(t-\sqrt{2\log\frac{1}{P(A)}}\Big)^2\Big),$$
--   where $A_t^c=\{x;\ f_c(A,x)\le t\}$ is the convex-hull enlargement of $A$.
--
--   The coefficient $\frac12$ of $t^2$ cannot be improved (Section 4.3 of the paper), and it is twice the coefficient $\frac14$ of the basic bound (4.1.3).
--
--   **Formalization Note** $P(A)>0$ is assumed: when $P(A)=0$, $\log(1/P(A))=+\infty$ and the paper's hypothesis on $t$ cannot hold. $A$ and every $x\mapsto f_\alpha(A,x)$, $\alpha>0$, are assumed measurable (the paper's convention of pp. 81–82); $P(A_t^c)$ is the outer probability. The bound is in $[0,\infty]$ with truncated subtraction.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 128, Corollary 4.2.5, Eq. (4.2.7)

import Mathlib
import Definitions.Def_TalagrandConc_ConvexHull_Basic

namespace TalagrandConc.ConvexHull

open MeasureTheory
open scoped ENNReal

/-- Talagrand (1995), p. 128, Corollary 4.2.5, Eq. (4.2.7): for `A ⊆ Ω^N` with `P(A) > 0`,
if `t ≥ √(2 log(1/P(A)))` then
`P(A_t^c) ≥ 1 − exp(−½ (t − √(2 log(1/P(A))))²)`.
Measurability convention (p. 81–82): `A` and every `x ↦ f_α(A, x)`, `α > 0`, are assumed
measurable; `P(A_t^c)` is the outer probability. `P(A) > 0` is the condition under which the
paper's hypothesis `t ≥ √(2 log(1/P(A)))` can hold at all. -/
theorem cor_4_2_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (A : Set (Fin N → Ω)) (hA : MeasurableSet A)
    (hmeas : ∀ α : ℝ, 0 < α → Measurable fun x => fAlpha α A x)
    (hpos : 0 < Measure.pi (fun _ : Fin N => μ) A) (t : ℝ)
    (ht : Real.sqrt (2 * Real.log (1 / (Measure.pi (fun _ : Fin N => μ) A).toReal)) ≤ t) :
    1 - ENNReal.ofReal (Real.exp (-(1 / 2 *
          (t - Real.sqrt (2 * Real.log (1 / (Measure.pi (fun _ : Fin N => μ) A).toReal))) ^ 2)))
      ≤ Measure.pi (fun _ : Fin N => μ) (enlarge A t) := by sorry

end TalagrandConc.ConvexHull
