-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_theorem_5_2
-- name    : PolymerEndpoint.Atomic.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:04.879262+00:00
-- url     : https://prove2.me/theorems/08a0bbf4-7779-4bea-9d57-325cfd15de8b
-- title:
--   Theorem 5.2 — fixed points in the two temperature phases
-- statement:
--   Under the standing model and moment assumptions, the fixed-point structure distinguishes the temperature regimes.
--
--   1. If $0\leq\beta\leq\beta_c$, then both the invariant-law set $\mathcal K$ and its minimizing subset $\mathcal M$ consist only of the point mass at the zero partitioned state.
--   2. If $\beta>\beta_c$, then every $\nu\in\mathcal M$ gives probability one to states of total mass one, and $\mathcal T$ has an invariant law distinct from the point mass at zero.
--
--   $$
--   \mathcal K=\mathcal M=\{\delta_{\mathbf0}\}\quad\text{in high temperature},\qquad
--   \nu\{f:\|f\|=1\}=1\quad(\nu\in\mathcal M)\quad\text{in low temperature}.
--   $$
--
--   This phase characterization is the bridge from free energy to endpoint localization.
--
--   **Formalization Note** The phases use the equivalent limiting free-energy characterization from Theorem A.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 38, Theorem 5.2

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace PolymerEndpoint.Atomic

theorem theorem_5_2 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 ≤ β) (hmom : MomentCondition 𝔏 β) :
    (HighTemp (d := d) 𝔏 β →
      K (d := d) 𝔏 β = {Measure.dirac (0 : PSM d)} ∧
      M (d := d) 𝔏 β = {Measure.dirac (0 : PSM d)}) ∧
    (LowTemp (d := d) 𝔏 β →
      (∀ ν ∈ M (d := d) 𝔏 β,
        ν {f : PSM d | mass f = 1} = 1) ∧
      ∃ ν ∈ K (d := d) 𝔏 β, ν ≠ Measure.dirac (0 : PSM d)) := by sorry

end PolymerEndpoint.Atomic
