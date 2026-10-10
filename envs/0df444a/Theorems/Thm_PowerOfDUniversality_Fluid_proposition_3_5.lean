-- Prove2me | Theorems.Thm_PowerOfDUniversality_Fluid_proposition_3_5
-- name    : PowerOfDUniversality.Fluid.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:13.39452+00:00
-- url     : https://prove2.me/theorems/b0275fae-999f-4e49-89bd-39a461764929
-- title:
--   Proposition 3.5 — two S-coupled systems from the same state stay within ℓ¹ distance 2Δ(t)
-- statement:
--   Fix $N\ge 1$ servers, a buffer $b\ge 1$ and an arrival rate $\lambda\ge 0$. Two S-coupled systems run arbitrary schemes $\Pi_1$ and $\Pi_2$ and start from the same occupancy state, $Q^{\Pi_1}_i(0)=Q^{\Pi_2}_i(0)$ for all $i$. At an arrival epoch the systems *differ in decision* if the arriving task joins different ordered positions in the two systems, and $\Delta_{\Pi_1,\Pi_2}(t)$ counts these epochs in $[0,t]$. Then almost surely
--   $$\sum_{i=1}^{b}\big|Q^{\Pi_1}_i(t)-Q^{\Pi_2}_i(t)\big|\le 2\,\Delta_{\Pi_1,\Pi_2}(t)\qquad\text{for all } t\ge 0 .$$
--
--   Two schemes whose decisions differ $o(N)$ times on finite intervals therefore have the same fluid limit.
--
--   **Formalization Note** The discarded-task counts do not enter (3.11). The schemes are required to select positions in $\{1,\dots,N\}$.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, p. 14, Proposition 3.5, (3.11)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid

/-- **Proposition 3.5** (p. 14, `ℓ¹` bound by the number of differing decisions). Two S-coupled
systems (`N ≥ 1` servers, buffer `b ≥ 1`, rate `λ ≥ 0`, the same clock and marks) run admissible
schemes `Π₁`, `Π₂` and start from the same occupancy state, `Q^{Π₁}(0) = Q^{Π₂}(0)`. Then almost
surely, for all `t ≥ 0`,
`∑_{i=1}^{b} |Q^{Π₁}_i(t) − Q^{Π₂}_i(t)| ≤ 2 Δ_{Π₁,Π₂}(t)`. -/
theorem proposition_3_5 (N : ℕ) (hN : 1 ≤ N) (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam : 0 ≤ lam)
    (pol₁ pol₂ : Scheme) (h₁ : IsScheme N pol₁) (h₂ : IsScheme N pol₂)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys₁ sys₂ : System P N b lam) (hξ : sys₁.ξ = sys₂.ξ) (hQ0 : ∀ ω, sys₁.Q0 ω = sys₂.Q0 ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      occDist (sys₁.occ pol₁ ω t) (sys₂.occ pol₂ ω t)
        ≤ 2 * sys₁.diffDecisions sys₂ pol₁ pol₂ ω t := by sorry

end PowerOfDUniversality.Fluid
