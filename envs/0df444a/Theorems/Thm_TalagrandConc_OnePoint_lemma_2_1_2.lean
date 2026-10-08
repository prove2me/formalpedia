-- Prove2me | Theorems.Thm_TalagrandConc_OnePoint_lemma_2_1_2
-- name    : TalagrandConc.OnePoint.lemma_2_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:48.011987+00:00
-- url     : https://prove2.me/theorems/f8d20a2a-1bd4-4f04-b0b5-2be72acf0831
-- title:
--   Lemma 2.1.2 — $\int\min(e^t,1/g)\,d\mu\int g\,d\mu\le a(t)$ for $0\le g\le 1$
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be a probability space and let $g:\Omega\to[0,1]$ be measurable. For every real $t$,
--   $$\int_\Omega \min\Big(e^t,\frac{1}{g(\omega)}\Big)\,d\mu(\omega)\ \int_\Omega g(\omega)\,d\mu(\omega)\ \le\ a(t),\qquad a(t)=\frac12+\frac{e^t+e^{-t}}{4},$$
--   where $\min(e^t,1/g(\omega))=e^t$ when $g(\omega)=0$.
--
--   This one-coordinate inequality is the whole content of Proposition 2.1.1: the induction over the number of coordinates reduces the $N$-dimensional bound to it, applied to $g(\omega)=P(A(\omega))/P(B)$.
--
--   **Formalization Note** Both integrals are lower Lebesgue integrals in $[0,\infty]$; $1/0=+\infty$ in `ℝ≥0∞`. The lemma is stated for every real $t$; for $t\le 0$ it holds trivially, and the paper uses it for $t>0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 82, Lemma 2.1.2, Eq. (2.1.4)

import Mathlib
import Definitions.Def_TalagrandConc_OnePoint_Basic

open MeasureTheory
open scoped ENNReal

namespace TalagrandConc.OnePoint

theorem lemma_2_1_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) (hg1 : ∀ ω, g ω ≤ 1) (t : ℝ) :
    (∫⁻ ω, min (ENNReal.ofReal (Real.exp t)) (ENNReal.ofReal (g ω))⁻¹ ∂μ) *
        (∫⁻ ω, ENNReal.ofReal (g ω) ∂μ) ≤ ENNReal.ofReal (aOne t) := by sorry

end TalagrandConc.OnePoint
