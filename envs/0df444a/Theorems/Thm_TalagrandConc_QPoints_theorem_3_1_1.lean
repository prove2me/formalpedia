-- Prove2me | Theorems.Thm_TalagrandConc_QPoints_theorem_3_1_1
-- name    : TalagrandConc.QPoints.theorem_3_1_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:23.769591+00:00
-- url     : https://prove2.me/theorems/b3e49835-72d3-472d-9ca9-115adcdce813
-- title:
--   Theorem 3.1.1 — $\int q^{f(A_1,\dots,A_q,x)}\,dP\le 1/\prod_{i\le q}P(A_i)$
-- statement:
--   Let $(\Omega,\mu)$ be a probability space, $N\ge0$ an integer, $P=\mu^{\otimes N}$ the product probability on $\Omega^N$, and $q\ge2$ an integer. For $A_1,\dots,A_q\subseteq\Omega^N$ let $f(A_1,\dots,A_q,x)$ be the smallest number of coordinates of $x$ not captured by points $y^1\in A_1,\dots,y^q\in A_q$ (Eq. (3.1.1)).
--
--   1. For measurable $A_1,\dots,A_q$,
--   $$\int q^{f(A_1,\dots,A_q,x)}\,dP(x)\le\frac{1}{\prod_{i\le q}P(A_i)} .$$
--   2. In particular, for a measurable $A\subseteq\Omega^N$ and every integer $k\ge0$,
--   $$P(\{f(A,\dots,A,x)\ge k\})\le\frac{1}{q^k\,P(A)^q} .$$
--
--   Here $q^{+\infty}=+\infty$ and $1/0=+\infty$, so an empty $A_i$ makes both sides infinite. The theorem says that a point drawn from a product measure is, with overwhelming probability, controlled by $q$ points of a set of non-negligible measure on all but a few coordinates, with a rate $q^{-k}$ that improves as $q$ grows.
--
--   **Formalization Note** Following the paper's convention of treating all sets and functions as measurable (Section 2.1), the sets are measurable and $x\mapsto f(A_1,\dots,A_q,x)$ is assumed measurable; integrals and probabilities are in $[0,\infty]$ (`∫⁻`, `ℝ≥0∞`). $\Omega^N$ is `Fin N → Ω` with `Measure.pi`. The integer $k$ is a natural number; the statement for real $k$ follows by rounding up.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 113, Theorem 3.1.1, Eqs. (3.1.2)–(3.1.3)

import Mathlib
import Definitions.Def_TalagrandConc_QPoints_Basic

namespace TalagrandConc.QPoints

open MeasureTheory
open scoped ENNReal

/-- Theorem 3.1.1: (3.1.2) and (3.1.3). -/
theorem theorem_3_1_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N q : ℕ) (hq : 2 ≤ q) :
    (∀ A : Fin q → Set (Fin N → Ω), (∀ i, MeasurableSet (A i)) →
        Measurable (qDist A) →
        ∫⁻ x, epow (q : ℝ≥0∞) (qDist A x) ∂(Measure.pi fun _ : Fin N => μ) ≤
          (∏ i : Fin q, (Measure.pi fun _ : Fin N => μ) (A i))⁻¹) ∧
    (∀ (A : Set (Fin N → Ω)) (k : ℕ), MeasurableSet A →
        Measurable (qDist (fun _ : Fin q => A)) →
        (Measure.pi fun _ : Fin N => μ) {x | (k : ℕ∞) ≤ qDist (fun _ : Fin q => A) x} ≤
          ((q : ℝ≥0∞) ^ k * (Measure.pi fun _ : Fin N => μ) A ^ q)⁻¹) := by sorry

end TalagrandConc.QPoints
