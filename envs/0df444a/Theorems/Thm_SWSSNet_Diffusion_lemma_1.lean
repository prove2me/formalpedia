-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_lemma_1
-- name    : SWSSNet.Diffusion.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:11.971462+00:00
-- url     : https://prove2.me/theorems/d7f7ceef-ceb5-49a3-945b-a8b76eff12f2
-- title:
--   Lemma 1 — inf over u^s ∈ Δ_J of 1 + ⟨e, B₁⁻¹B₂u^s⟩ is positive
-- statement:
--   Let $B_1,B_2$ be the matrices of (38) for a pool $\hat\jmath$. There is a constant $c>0$ such that
--   $$
--   1+\langle e,B_1^{-1}B_2u^s\rangle\ \ge\ c\qquad\text{for every }u^s\in\Delta_J,
--   $$
--   that is, $\inf_{u^s\in\Delta_J}\big(1+\langle e,B_1^{-1}B_2u^s\rangle\big)>0$.
--
--   In the drift of the test function used in Theorem 5, this quantity multiplies the number of idle servers $\langle e,x\rangle^-$. Its positivity makes that contribution nonnegative under every control.
--
--   **Formalization Note** The paper's $\Delta_s$ is $\Delta_J$ of (34). The infimum over the compact simplex is written as a uniform positive lower bound.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 22, Lemma 1

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Lemma 1, p. 22: for the matrices `B₁, B₂` of any pool `ĵ`,
`inf_{u^s ∈ ∆_J} (1 + ⟨e, B₁⁻¹B₂u^s⟩) > 0`. -/
theorem lemma_1 {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) :
    ∃ c : ℝ, 0 < c ∧ ∀ us ∈ stdSimplex ℝ (Fin J),
      c ≤ 1 + ∑ i, ((B1 N ĵ)⁻¹ *ᵥ (B2 N ĵ *ᵥ us)) i := by sorry

end SWSSNet.Diffusion
