-- Prove2me | Theorems.Thm_TalagrandConc_TSP_gaussian_concentration
-- name    : TalagrandConc.TSP.gaussian_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:28.671348+00:00
-- url     : https://prove2.me/theorems/a4838d0d-f651-4c8c-a41c-c66fa869e94a
-- title:
--   Theorem 11.2.2 — Gaussian concentration of regular geometric functionals
-- statement:
--   Fix a regularity constant $K_0>0$. There is a constant $K>0$, depending on $K_0$ but independent of the sample size and the functional, with the following property. Let $X_1,\ldots,X_N$ be independent uniform points in $[0,1]^2$, $N\ge1$, and let $L$ be a measurable real-valued functional of their set of distinct locations. Suppose that for every dyadic square $C$ of side $2^{-k}$, $k\ge1$, finite $F$, and finite $G\subseteq C$, if a point of $F$ is within distance $2^{-k+2}$ of $C$, then
--   $$L(F)\le L(F\cup G)\le L(F)+K_0,2^{-k}\sqrt{|G|}.$$
--   If $M$ is any median of $L_N=L(\{X_1,\ldots,X_N\})$, then for every $t\ge0$,
--   $$P(|L_N-M|\ge t)\le K\exp(-t^2/K).$$
--
--   This gives dimension-free fluctuation control for the Euclidean traveling salesman tour length, which satisfies the stated regularity condition, and for other functionals with the same condition.
--
--   **Formalization Note** The event is measured in the product of uniform laws on the square. The statement explicitly requires measurability of the sample functional, following the paper's convention. It quantifies the constant before $N$ and $L$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 175, Theorem 11.2.2

import Mathlib
import Definitions.Def_TalagrandConc_TSP_Basic

namespace TalagrandConc.TSP

open MeasureTheory

/-- Talagrand (1995), Theorem 11.2.2, p. 175. The constant is uniform in
the sample size and the functional, for each fixed regularity constant. -/
theorem gaussian_concentration (K₀ : ℝ) (hK₀ : 0 < K₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (_ : 0 < N) (L : Finset Point → ℝ),
      Regular K₀ L → Measurable (fun x : Fin N → Point => L (sampleSet x)) →
      ∀ (M : ℝ), IsMedian (N := N) L M → ∀ (t : ℝ), 0 ≤ t →
        sampleLaw N {x | t ≤ |L (sampleSet x) - M|} ≤
          ENNReal.ofReal (K * Real.exp (-(t ^ 2) / K)) := by sorry

end TalagrandConc.TSP
