-- Prove2me | Theorems.Thm_TalagrandConc_QPoints_eq_3_2_1
-- name    : TalagrandConc.QPoints.eq_3_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:29.668193+00:00
-- url     : https://prove2.me/theorems/8fe33c44-17c0-4262-963c-5faaf1bd5cf2
-- title:
--   Eq. (3.2.1) — $\int a(q,\alpha)^{f(A_1,\dots,A_q,x)}\,dP\le 1/\prod_{i\le q}P(A_i)^\alpha$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $P=\mu^{\otimes N}$ on $\Omega^N$, $q\ge2$ an integer, $\alpha>1$, and $a(q,\alpha)$ the unique $x>1$ with $x+q\alpha x^{-1/\alpha}=1+q\alpha$ (Eq. (3.2.2)). For measurable $A_1,\dots,A_q\subseteq\Omega^N$,
--   $$\int a(q,\alpha)^{f(A_1,\dots,A_q,x)}\,dP(x)\le\frac1{\prod_{i\le q}P(A_i)^{\alpha}},$$
--   where $f$ is the $q$-point control of (3.1.1).
--
--   This trades a worse power of $1/P(A_i)$ for a larger base than $q$, which is what yields the large-$q$ bound of Proposition 3.2.1.
--
--   **Formalization Note** The paper prints the left side as an upper integral $\int^*$; following its convention (Section 2.1) the formal statement assumes $x\mapsto f(A_1,\dots,A_q,x)$ measurable and uses `∫⁻`. Powers and the inverse are in `ℝ≥0∞`, so an empty $A_i$ makes the right side $+\infty$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 114, Eq. (3.2.1) with (3.2.2)

import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic
import Definitions.Def_TalagrandConc_QPoints_aConst

namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal

/-- (3.2.1) with `a(q, α)` of (3.2.2), for `α > 1`. -/
theorem eq_3_2_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N q : ℕ) (hq : 2 ≤ q) (α : ℝ) (hα : 1 < α) (A : Fin q → Set (Fin N → Ω))
    (hA : ∀ i, MeasurableSet (A i)) (hf : Measurable (qDist A)) :
    ∫⁻ x, epow (ENNReal.ofReal (aConst q α)) (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
      (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i) ^ α)⁻¹ := by sorry

end TalagrandConc.QPoints
