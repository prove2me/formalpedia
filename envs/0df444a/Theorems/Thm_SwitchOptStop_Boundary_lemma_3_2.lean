-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_lemma_3_2
-- name    : SwitchOptStop.Boundary.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:38.672542+00:00
-- url     : https://prove2.me/theorems/145762c8-ef20-4d5c-8d81-692edfe40d2a
-- title:
--   Lemma 3.2, p. 8 — for large N the first entry time of D^N is a.s. finite, hence so are τ_D and τ_{D^N_ε}
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. There is $N_0$ such that for every $N>N_0$, every regime $\iota$ and every $x\in(0,\infty)^2$, under $\mathsf P_{\iota,x}$:
--   $$
--   \tau_{D^N}<\infty,\qquad \tau_D<\infty,\qquad \tau_{D^N_\varepsilon}<\infty\ \ (\varepsilon>0)\qquad\text{almost surely},
--   $$
--   where $D^N=\{V^N\ge0\}$, $D^N_\varepsilon=\{V^N\ge-\varepsilon\}$ and $D=\{V=0\}$.
--
--   Finiteness of these entry times is what makes the approximation $N\to\infty$ of Section 3 work.
--
--   **Formalization Note** The page states no condition on $N$; its proof uses Proposition 2.4, which requires $N$ large, so the Lean statement carries $\exists N_0\,\forall N>N_0$.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 8, Lemma 3.2

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Lemma 3.2 (p. 8): for `N` large, the first entry time of `D^N` is finite almost surely, hence so
are those of `D` and of `D^N_ε`. -/
theorem lemma_3_2 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S) :
    ∃ N0 : ℝ, ∀ N : ℝ, N0 < N → ∀ ι : Fin 2, ∀ x ∈ openQuadrant,
      (∀ᵐ ω ∂(Pι S ι), entryTime S x (stopSetN m S N 0) ω < ⊤) ∧
      (∀ᵐ ω ∂(Pι S ι), entryTime S x (stopSet m S) ω < ⊤) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂(Pι S ι), entryTime S x (stopSetN m S N ε) ω < ⊤ := by sorry

end SwitchOptStop.Boundary
