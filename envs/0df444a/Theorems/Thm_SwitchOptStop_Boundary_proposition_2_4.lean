-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_proposition_2_4
-- name    : SwitchOptStop.Boundary.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:32.53068+00:00
-- url     : https://prove2.me/theorems/b13c5634-d427-4bd9-850b-5e123870320c
-- title:
--   Proposition 2.4, p. 5 — for large N the 1-d problem (2.7) stops on {z ≥ x̄¹_ι}, x̄¹_ι ∈ (0, ∞), and its first entry time is optimal and a.s. finite
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. Consider the one-dimensional problem
--   $$
--   \tilde V^{1,N}(\iota,z)=\inf_\tau\mathsf E_{\iota,z}\int_0^\tau e^{-\int_0^t\lambda(\alpha_s)ds}H^N(\alpha_t,(\tilde X^1_t,0))\,dt.
--   $$
--   Then there is $N_0$ such that for every $N>N_0$ there are finite positive thresholds $\bar x^1_1,\bar x^1_2$ with:
--
--   1. $\tilde V^{1,N}(\iota,z)=0$ if and only if $z\ge\bar x^1_\iota$, for all $\iota$ and $z>0$; that is, the stopping region $\{(\iota,z):\tilde V^{1,N}(\iota,z)=0\}$ has the form $\{z\ge\bar x^1_\iota\}$;
--   2. the first entry time of $(\alpha,\tilde X^1)$ into this region is a stopping time and is optimal for $\tilde V^{1,N}$;
--   3. this entry time is finite almost surely.
--
--   The thresholds feed the bounds on the two-dimensional stopping boundaries (Lemma 3.6, Proposition 3.7).
--
--   **Formalization Note** "Let $N>0$ be large" is $\exists N_0\,\forall N>N_0$. Statement (1) of the paper, "the optimal stopping region is $\{\tilde V^{1,N}=0\}$", is stated as optimality of the first entry time into that region, in `EReal`.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 5, Proposition 2.4

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Proposition 2.4 (p. 5): for `N` large, the stopping region of the one-dimensional problem (2.7)
is `{Ṽ^{1,N} = 0} = {z ≥ x̄¹_ι}` with finite positive thresholds, its first entry time is an optimal
stopping time, and it is finite almost surely. -/
theorem proposition_2_4 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S) :
    ∃ N0 : ℝ, ∀ N : ℝ, N0 < N →
      ∃ xb : Fin 2 → ℝ, (∀ ι, 0 < xb ι) ∧
        ∀ ι : Fin 2, ∀ z : ℝ, 0 < z →
          (value1N m S N ι z = 0 ↔ xb ι ≤ z) ∧
          IsStoppingTime (S.𝔾₁ z)
            (entryTime1 S z (fun κ => {y | 0 < y ∧ value1N m S N κ y = 0})) ∧
          value1NE m S N ι z = costJ (Pι S ι) (cost1N m S N z)
            (entryTime1 S z (fun κ => {y | 0 < y ∧ value1N m S N κ y = 0})) ∧
          ∀ᵐ ω ∂(Pι S ι),
            entryTime1 S z (fun κ => {y | 0 < y ∧ value1N m S N κ y = 0}) ω < ⊤ := by sorry

end SwitchOptStop.Boundary
