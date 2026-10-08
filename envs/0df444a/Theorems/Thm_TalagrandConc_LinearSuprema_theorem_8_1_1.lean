-- Prove2me | Theorems.Thm_TalagrandConc_LinearSuprema_theorem_8_1_1
-- name    : TalagrandConc.LinearSuprema.theorem_8_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:38.81008+00:00
-- url     : https://prove2.me/theorems/3d835d52-df1e-4df3-be75-1c6ba01f32b6
-- title:
--   Theorem 8.1.1 — Gaussian concentration of a linear supremum
-- statement:
--   Let $\mathcal F$ be a nonempty family of real $N$-tuples with finite, positive
--   $\sigma=\sup_{\alpha\in\mathcal F}\|\alpha\|_2$. Let $X_1,\ldots,X_N$ be independent real
--   random variables, with $r_i\le X_i\le r_i+1$ almost surely for each $i$, and put
--   $$Z=\sup_{\alpha\in\mathcal F}\sum_{i=1}^N\alpha_iX_i.$$
--   Assume $Z$ is measurable, and let $M$ be any median of $Z$. For every $u>0$,
--   $$P(|Z-M|\ge u)\le4\exp\left(-\frac{u^2}{4\sigma^2}\right).$$
--
--   The bound gives Gaussian-scale concentration for an arbitrary, possibly infinite family
--   of linear forms and does not require identical coordinate laws.
--
--   **Formalization Note** The independent variables are represented on their canonical product
--   space. The assumptions that $\mathcal F$ is nonempty, $\sigma$ is finite and positive, and
--   $Z$ is measurable make the paper's implicit real-valued probability statement precise.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 156, Theorem 8.1.1, Eq. (8.1.1)

import Mathlib
import Definitions.Def_TalagrandConc_LinearSuprema_Basic

namespace TalagrandConc.LinearSuprema

theorem theorem_8_1_1 {N : ℕ} (F : Set (Fin N → ℝ))
    (hF : F.Nonempty) (hσfinite : BddAbove (coeffNorm '' F))
    (hσ : 0 < sigma F) (r : Fin N → ℝ)
    (μ : Fin N → MeasureTheory.Measure ℝ)
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, μ i (Set.Icc (r i) (r i + 1)) = 1)
    (hZmeas : Measurable (linearSupremum F))
    (M : ℝ)
    (hM : TalagrandConc.BinPacking.IsMedian (MeasureTheory.Measure.pi μ) (linearSupremum F) M)
    (u : ℝ) (hu : 0 < u) :
    (MeasureTheory.Measure.pi μ) {x | |linearSupremum F x - M| ≥ u} ≤
      ENNReal.ofReal (4 * Real.exp (-(u ^ 2) / (4 * (sigma F) ^ 2))) := by sorry

end TalagrandConc.LinearSuprema
