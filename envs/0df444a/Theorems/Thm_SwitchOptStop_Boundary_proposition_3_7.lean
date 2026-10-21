-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_proposition_3_7
-- name    : SwitchOptStop.Boundary.proposition_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:46.664886+00:00
-- url     : https://prove2.me/theorems/899febcd-a3c4-4bc1-b427-7586db4ed4ea
-- title:
--   Proposition 3.7, p. 11 — b_ι is decreasing, convex, continuous and bounded; H(ι, z, b_ι(z)) ≥ 0; D_ι is an up-set; b_ι = 0 beyond x̄¹_ι
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. For each regime $\iota$:
--
--   1. $b_\iota$ is decreasing, convex and continuous on $(0,\infty)$, with $b_\iota(0+)<\infty$;
--   2. $H(\iota,(z,b_\iota(z)))\ge0$ for every $z>0$;
--   3. if $(x_1,x_2)\in D_\iota$ and $\bar x_1\ge x_1$, $\bar x_2\ge x_2$, then $(\bar x_1,\bar x_2)\in D_\iota$;
--   4. for $N$ large, $b_\iota(z)=0$ whenever $z\ge\bar x^1_\iota$, the threshold of the one-dimensional problem (2.7).
--
--   These are the shape properties of the optimal stopping boundary used in Theorem 3.8 and in the admissible class of Theorem 5.1.
--
--   **Formalization Note** $b_\iota(0+)<\infty$ for a decreasing function is boundedness on $(0,\infty)$. Statement (2) is posed for $z>0$: the page writes $z\in[0,\infty)$, but $b_\iota(0)$ is not defined since $V$ lives on $(0,\infty)^2$. Statement (4) uses $\bar x^1_\iota$: the page prints $\bar x^2_\iota$, which it never defines; the cited argument (proof of Lemma 3.6) gives the statement with $\bar x^1_\iota$, for $N>N_0$.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 11, Proposition 3.7

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Proposition 3.7 (p. 11): properties of the optimal stopping boundary `b_ι`. Statement (4) uses the
threshold `x̄¹_ι` of (2.7) (the page prints the undefined `x̄²_ι`), for `N` large. -/
theorem proposition_3_7 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S) :
    ∀ ι : Fin 2,
      (AntitoneOn (bdry m S ι) (Ioi 0) ∧ ConvexOn ℝ (Ioi 0) (bdry m S ι) ∧
        ContinuousOn (bdry m S ι) (Ioi 0) ∧ BddAbove (bdry m S ι '' Ioi 0)) ∧
      (∀ z : ℝ, 0 < z → 0 ≤ m.H ι ![z, bdry m S ι z]) ∧
      (∀ x ∈ stopSet m S ι, ∀ x' : Pt, x ≤ x' → x' ∈ stopSet m S ι) ∧
      (∃ N0 : ℝ, ∀ N : ℝ, N0 < N → ∀ z : ℝ, 0 < z → xbar1 m S N ι ≤ z → bdry m S ι z = 0) := by sorry

end SwitchOptStop.Boundary
