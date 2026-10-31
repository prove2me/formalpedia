-- Prove2me | Theorems.Thm_RiskExpPG_corollary_16
-- name    : RiskExpPG.corollary_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:18.84304+00:00
-- url     : https://prove2.me/theorems/06c65576-966b-4db4-ac45-8009af2fa67f
-- title:
--   Corollary 16 — $\nabla_\theta\Lambda^{(M)}_\theta\to\nabla_\theta\Lambda_\theta$ uniformly
-- statement:
--   $\nabla_\theta\Lambda^{(M)}_\theta\to\nabla_\theta\Lambda_\theta$ as $M\uparrow\infty$, uniformly over $\theta\in\mathbb R^l$: for every $\varepsilon>0$ there is $M_0>1$ such that $\|\nabla_\theta\Lambda^{(M)}_\theta-\nabla_\theta\Lambda_\theta\|<\varepsilon$ for all $M\ge M_0$ and all $\theta$.
--
--   So a stationary point of the truncated cost is close to a stationary point of the cost, uniformly in $\theta$.
--
--   Differences from the source:
--   - reading: no assumptions named in the statement → Assumptions 1 to 3; reason: the proofs in App. E cite them (Lemma 14's proof, p.40) and they are the standing assumptions of Theorem 1
--   - reading: bounded functions and bounded derivatives in Assumptions 2 and 3 → bounds uniform in θ, with no continuity of the second derivative; reason: Lemma 12's proof and Lemma 17 need uniform bounds; the page says twice differentiable, not C²
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
--   - reading: ∇_θ Λ^(M)_θ ↑ ∇_θ Λ_θ → uniform convergence of the vectors, with M₀ independent of θ; reason: a vector has no monotone order here, and the proof shows uniform convergence
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Corollary 16, p.43

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model
open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Corollary 16** (arXiv:2202.04157v2, p.43). `∇_θ Λ^(M)_θ → ∇_θ Λ_θ` as `M ↑ ∞`, uniformly over
`θ ∈ ℝ^l`. -/
theorem corollary_16 {X : Type*} [Fintype X] [DecidableEq X] {l : ℕ} (m : Model X l)
    (hm : m.IsValid) (h1 : m.Assumption1) (h2 : m.Assumption2) (h3 : m.Assumption3) :
    ∀ ε > 0, ∃ M₀ > 1, ∀ M ≥ M₀, ∀ θ,
      ‖gradient (m.truncCost M) θ - gradient m.riskCost θ‖ < ε := by sorry

end RiskExpPG
