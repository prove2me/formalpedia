-- Prove2me | Theorems.Thm_ProbEffIS_GE_theorem_6
-- name    : ProbEffIS.GE.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:46.191984+00:00
-- url     : https://prove2.me/theorems/cb2f49ab-92fb-4ff4-8ee4-1ee693303889
-- title:
--   Theorem 6 — most significant dominating points suffice
-- statement:
--   Let $\nu_\gamma$ be the laws of $X_\gamma$, let $\mathcal E$ satisfy Assumptions 1 and 2, and let $A$ be a finite dominating set. Select exactly its lowest-rate points $a_i$, whose rates are equal and strictly below those of every point left out. Give them fixed positive weights $\alpha_i$ summing to one, and form the exponential-tilt mixture of equation (11). Its importance-sampling output is strongly probabilistically efficient:
--
--   $$
--   \exists n(\gamma)\ge1:\quad \frac{\log n(\gamma)}{-\log p_\gamma}\to0,\qquad
--   \forall\varepsilon>0,\quad\delta_\varepsilon(\hat p_\gamma,p_\gamma)\to0.
--   $$
--
--   This is the paper’s main result: sampling toward every dominating point is unnecessary for this probability-based efficiency criterion. The mixture retains every most significant point, including ties.
--
--   **Formalization Note** The laws live on Euclidean space and the selected indices form a nonempty finite set. The likelihood ratio is the explicit reciprocal of the tilted-density mixture.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, p. 20, Theorem 6 and equation (11)

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE

/-- Theorem 6, p. 20: tilts only toward the most significant points suffice. -/
theorem theorem_6 {d r : ℕ} (ν : ℝ → Measure (Rd d))
    [∀ γ, IsProbabilityMeasure (ν γ)]
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (R : Set (Rd d)) (h2 : Assumption2 μ R)
    (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s)
    (S : Finset (Fin r)) (hS : IsMostSignificant μ a S)
    (α : Fin r → ℝ) (hα : ∀ i ∈ S, 0 < α i)
    (hα1 : ∑ i ∈ S, α i = 1) :
    StronglyProbEfficient
      (fun γ => mixtureIS ν γ S α s)
      (fun γ => isOutput ν γ R S α s)
      (fun γ => rareProb ν γ R) := by sorry

end ProbEffIS.GE
