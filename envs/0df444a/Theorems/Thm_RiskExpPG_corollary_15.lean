-- Prove2me | Theorems.Thm_RiskExpPG_corollary_15
-- name    : RiskExpPG.corollary_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:31.339831+00:00
-- url     : https://prove2.me/theorems/b331f6cb-e74d-45f8-8fd8-8152ddec81e0
-- title:
--   Corollary 15 — the first and second gradients of $\Lambda^{(M)}_\theta$ and $\Lambda_\theta$ are uniformly bounded
-- statement:
--   The functions $\nabla_\theta\Lambda^{(M)}_\theta$, $\nabla^2_\theta\Lambda^{(M)}_\theta$, $\nabla_\theta\Lambda_\theta$ and $\nabla^2_\theta\Lambda_\theta$ are uniformly bounded over $\theta\in\mathbb R^l$ and $M>1$.
--
--   This smoothness, uniform in the truncation level, is what allows a second-order expansion of the cost along the iterates.
--
--   Differences from the source:
--   - reading: no assumptions named in the statement → Assumptions 1 to 3; reason: the proofs in App. E cite them (Lemma 14's proof, p.40) and they are the standing assumptions of Theorem 1
--   - reading: bounded functions and bounded derivatives in Assumptions 2 and 3 → bounds uniform in θ, with no continuity of the second derivative; reason: Lemma 12's proof and Lemma 17 need uniform bounds; the page says twice differentiable, not C²
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
--   - encoding: the gradients are uniformly bounded → Λ^(M) and Λ are twice differentiable, with one bound B; reason: a bound on a junk gradient would say nothing
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Corollary 15, p.43

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model
open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Corollary 15** (arXiv:2202.04157v2, p.43). `Λ^(M)` and `Λ` are twice differentiable, and
`∇_θ Λ^(M)_θ`, `∇²_θ Λ^(M)_θ`, `∇_θ Λ_θ`, `∇²_θ Λ_θ` are uniformly bounded over `θ ∈ ℝ^l` and `M > 1`. -/
theorem corollary_15 {X : Type*} [Fintype X] [DecidableEq X] {l : ℕ} (m : Model X l)
    (hm : m.IsValid) (h1 : m.Assumption1) (h2 : m.Assumption2) (h3 : m.Assumption3) :
    (∀ M, 1 < M →
      Differentiable ℝ (m.truncCost M) ∧ Differentiable ℝ (fderiv ℝ (m.truncCost M))) ∧
    Differentiable ℝ m.riskCost ∧
    Differentiable ℝ (fderiv ℝ m.riskCost) ∧
    ∃ B : ℝ, ∀ θ,
      (∀ M, 1 < M →
        ‖gradient (m.truncCost M) θ‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (m.truncCost M)) θ‖ ≤ B) ∧
      ‖gradient m.riskCost θ‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ m.riskCost) θ‖ ≤ B := by sorry

end RiskExpPG
