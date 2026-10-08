-- Prove2me | Theorems.Thm_TalagrandConc_QPoints_proposition_3_2_1
-- name    : TalagrandConc.QPoints.proposition_3_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:37.242976+00:00
-- url     : https://prove2.me/theorems/52c1c44a-b2bc-42bb-ad61-fecd5db149f1
-- title:
--   Proposition 3.2.1 — $P(f(A,\dots,A,x)\ge k)\le\big(\frac{e}{(e-1)q\log q}\big)^k P(A)^{-q\log q}$ for $q\ge q_0$
-- statement:
--   There exists a universal constant $q_0$ with the following property. Let $q\ge q_0$ be an integer (with $q\ge2$), $(\Omega,\mu)$ a probability space, $N\ge0$, $P=\mu^{\otimes N}$, and $A\subseteq\Omega^N$ measurable. Then for every integer $k\ge0$,
--   $$P(\{f(A,\dots,A,x)\ge k\})\le\Big(\frac{e}{(e-1)\,q\log q}\Big)^k\Big(\frac1{P(A)}\Big)^{q\log q},$$
--   where $f(A,\dots,A,x)$ is the $q$-point control (3.1.1) with all $q$ sets equal to $A$ and $\log$ is the natural logarithm.
--
--   For $k$ much larger than $q\log q$ this improves (3.1.3) by a factor of order $\log q$ in the base, and Talagrand shows it is sharp up to a universal constant in the base.
--
--   **Formalization Note** $q_0$ is quantified before $\Omega$, $\mu$, $N$, $A$, $k$, so it is uniform over all of them. Following the paper's measurability convention, $x\mapsto f(A,\dots,A,x)$ is assumed measurable; probabilities are in `ℝ≥0∞`, with $1/0=\infty$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 114, Proposition 3.2.1, Eq. (3.2.4)

import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic

universe u

namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal

/-- Proposition 3.2.1 (3.2.4): a universal `q₀` such that for every integer `q ≥ q₀`
(and `q ≥ 2`, the standing assumption of Section 3) the bound holds on every product
probability space. `log` is the natural logarithm. -/
theorem proposition_3_2_1 :
    ∃ q₀ : ℝ, ∀ (q : ℕ), 2 ≤ q → q₀ ≤ (q : ℝ) →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
        (A : Set (Fin N → Ω)) (k : ℕ), MeasurableSet A →
        Measurable (qDist (fun _ : Fin q => A)) →
        (Measure.pi fun _ : Fin N => μ) {x | (k : ℕ∞) ≤ qDist (fun _ : Fin q => A) x} ≤
          ENNReal.ofReal (Real.exp 1 / ((Real.exp 1 - 1) * q * Real.log q)) ^ k *
            ((Measure.pi fun _ : Fin N => μ) A)⁻¹ ^ ((q : ℝ) * Real.log q) := by sorry

end TalagrandConc.QPoints
