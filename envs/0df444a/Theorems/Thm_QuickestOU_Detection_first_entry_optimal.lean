-- Prove2me | Theorems.Thm_QuickestOU_Detection_first_entry_optimal
-- name    : QuickestOU.Detection.first_entry_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:37.556572+00:00
-- url     : https://prove2.me/theorems/600de667-1a6a-453d-9b2a-03a5eabf87c9
-- title:
--   §7 items 1 and 3 — first entry into D is finite and optimal
-- statement:
--   Let $D=\{(\varphi,x):\widehat V(\varphi,x)=0\}$ be the stopping region and let $\tau_D$ be the first entry time of $(\Phi,X)$ into $D$. For every $\varphi\ge0$ and $x\in\mathbb R$, $\tau_D$ is a stopping time, is finite almost surely under the no-change law, and attains the value:
--
--   $$\mathsf E^\infty_{\varphi,x}\!\left[\int_0^{\tau_D}e^{-\lambda t}(\Phi_t-\lambda/c)\,dt\right]=\widehat V(\varphi,x).$$
--
--   This gives a canonical optimal rule before the boundary is characterized as a graph.
--
--   **Formalization Note** The expected signed integral is represented by a difference of two nonnegative extended integrals.
-- source:
--   Glover & Peskir, Quickest detection problems for Ornstein–Uhlenbeck processes, Research Report No. 11 (2017, revised), Probab. Statist. Group Manchester; to appear in Math. Oper. Res.; https://doi.org/10.1287/moor.2021.0186; pp. 15–16, §7 items 1 and 3, (7.3)

import Mathlib
import Definitions.Def_QuickestOU_Detection_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuickestOU.Detection

/-- §7 items 1 and 3: first entry into D is almost surely finite and optimal. -/
theorem first_entry_optimal (P : Params) (hS : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : Driver μ B) (phi x : ℝ) (hphi : 0 ≤ phi) :
    IsStoppingTime (natB B hB.meas) (entryD P B μ hB.meas phi x) ∧
    (∀ᵐ ω ∂μ, entryD P B μ hB.meas phi x ω ≠ ⊤) ∧
    payoff P B μ phi x (entryD P B μ hB.meas phi x) =
      Vhat P B μ hB.meas phi x := by sorry

end QuickestOU.Detection
