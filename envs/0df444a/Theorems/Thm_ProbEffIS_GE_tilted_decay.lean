-- Prove2me | Theorems.Thm_ProbEffIS_GE_tilted_decay
-- name    : ProbEffIS.GE.tilted_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:50.127031+00:00
-- url     : https://prove2.me/theorems/af870d79-dc06-4b2c-ab6f-6e4c33a19039
-- title:
--   Proof of Theorems 5 and 6 — omitted events decay under each tilt
-- statement:
--   With the same selected set $S$ and residual rate $I_{\mathrm{out}}$, let $\widetilde P_{\gamma,i}$ be the exponential tilt toward $a_i$ for $i\in S$. Then
--
--   $$
--   \limsup_{\gamma\to\infty}\gamma^{-1}\log\widetilde P_{\gamma,i}(\gamma^{-1}X_\gamma\in\mathcal E_2)\le-\bigl(I_{\mathrm{out}}-I(a_i)\bigr)<0.
--   $$
--
--   The positive rate gap shows that the omitted region is exponentially unlikely under each selected tilt, giving the third condition of Theorem 3. The result concerns each component of the mixture, with the common lowest rate on $S$.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, p. 22, proof of Theorems 5 and 6

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE

/-- The exponentially small omitted-event probability under each selected tilt,
    proof of Theorems 5–6, p. 22. -/
theorem tilted_decay {d r : ℕ} (ν : ℝ → Measure (Rd d))
    [∀ γ, IsProbabilityMeasure (ν γ)]
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (R : Set (Rd d)) (h2 : Assumption2 μ R)
    (a s : Fin r → Rd d) (hA : IsDominatingSet μ R a s)
    (S : Finset (Fin r)) (hS : IsMostSignificant μ a S)
    (hSne : S ≠ Finset.univ) :
    let Iout : EReal := ⨅ j ∈ (Finset.univ \ S), rate μ (a j)
    ∀ i ∈ S,
      limsup (fun γ : ℝ => ((γ⁻¹ : ℝ) : EReal) *
        ENNReal.log ((ν γ).tilted (fun x => inner ℝ (s i) x)
          {x | γ⁻¹ • x ∈ splitOut R S a s})) atTop ≤
        -(Iout - rate μ (a i)) ∧
      0 < Iout - rate μ (a i) := by sorry

end ProbEffIS.GE
