-- Prove2me | Theorems.Thm_ProbEffIS_GE_p2_decay
-- name    : ProbEffIS.GE.p2_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:52.436817+00:00
-- url     : https://prove2.me/theorems/cb1c6d8a-a637-4a59-bce1-3912b32179fe
-- title:
--   Proof of Theorems 5 and 6 — neglected original probability decays faster
-- statement:
--   Let $S$ contain exactly the dominating points with lowest rate, and suppose at least one other point remains. Let $\mathcal E_2$ be the part of the rare set missed by the half-spaces for $S$, and let $I_{\mathrm{out}}$ be the least rate among the remaining dominating points. Then
--
--   $$
--   \limsup_{\gamma\to\infty}\gamma^{-1}\log p_2\le-I_{\mathrm{out}}<-I(\mathcal E),\qquad p_2/p\longrightarrow0.
--   $$
--
--   This verifies the first condition of Theorem 3 for the main theorem’s rare-event split. The finite infimum over the remaining points represents the paper’s $I(a_{k+1})$.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, p. 21, proof of Theorems 5 and 6

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE

/-- The decay of the neglected rare-event probability, proof of Theorems 5–6, p. 21. -/
theorem p2_decay {d r : ℕ} (ν : ℝ → Measure (Rd d))
    [∀ γ, IsProbabilityMeasure (ν γ)]
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (R : Set (Rd d)) (h2 : Assumption2 μ R)
    (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s)
    (S : Finset (Fin r)) (hS : IsMostSignificant μ a S)
    (hSne : S ≠ Finset.univ) :
    let Iout : EReal := ⨅ j ∈ (Finset.univ \ S), rate μ (a j)
    limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
      ENNReal.log (ν γ {x | γ⁻¹ • x ∈ splitOut R S a s})) atTop ≤ -Iout ∧
    -Iout < -(rateOn μ R) ∧
    Tendsto (fun γ => rareProb ν γ (splitOut R S a s) / rareProb ν γ R)
      atTop (𝓝 0) := by sorry

end ProbEffIS.GE
