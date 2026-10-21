-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_lemma_3_6
-- name    : SwitchOptStop.Boundary.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:34.415134+00:00
-- url     : https://prove2.me/theorems/22c8d0e5-f2ae-4249-91be-601a6f10b739
-- title:
--   Lemma 3.6, p. 10 — for N > N0, b_ι(z) ≤ b^N_ι(z) < ∞ for z > 0, and P_{ι,x}(τ_D < ∞) = 1
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. There is $N_0$ such that for every $N>N_0$, every $\iota$ and every $z>0$,
--   $$
--   b_\iota(z)\le b^N_\iota(z)<\infty,
--   $$
--   where $b^N_\iota(z)<\infty$ means that $V^N(\iota,z,x_2)=0$ for some $x_2>0$. Moreover $\mathsf P_{\iota,x}(\tau_D<\infty)=1$ for all $(\iota,x)\in M\times(0,\infty)^2$.
--
--   The truncated boundaries dominate the true ones, which gives finiteness of $b_\iota$ and of the optimal stopping time.
--
--   **Formalization Note** The page prints the strict inequality $b_\iota(z)<b^N_\iota(z)$. It fails where both boundaries vanish: for $z>\bar x^1_\iota$ the proof itself shows $V^N(\iota,z,0)\ge0$, hence $b^N_\iota(z)=b_\iota(z)=0$. The proof establishes $D^N\subset D$, which is the non-strict inequality stated here.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 10, Lemma 3.6

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Lemma 3.6 (p. 10), with the printed `b_ι(z) < b^N_ι(z)` corrected to `≤`: for `N` large and
every `z > 0`, `b_ι(z) ≤ b^N_ι(z) < ∞`; and `τ_D < ∞` almost surely from every starting point. -/
theorem lemma_3_6 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S) :
    (∃ N0 : ℝ, ∀ N : ℝ, N0 < N → ∀ ι : Fin 2, ∀ z : ℝ, 0 < z →
      bdry m S ι z ≤ bdryN m S N ι z ∧ ∃ x2 : ℝ, 0 < x2 ∧ valueN m S N ι ![z, x2] = 0) ∧
    ∀ ι : Fin 2, ∀ x ∈ openQuadrant,
      Pι S ι {ω | entryTime S x (stopSet m S) ω < ⊤} = 1 := by sorry

end SwitchOptStop.Boundary
