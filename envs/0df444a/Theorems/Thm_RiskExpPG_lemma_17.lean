-- Prove2me | Theorems.Thm_RiskExpPG_lemma_17
-- name    : RiskExpPG.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:17.068998+00:00
-- url     : https://prove2.me/theorems/88b2ac0d-4ef2-4ac9-aad3-bda2b56d1f9c
-- title:
--   Lemma 17 — uniform bounds on $g$, $g^{(M)}$ and their derivatives near $\Lambda_\theta$, and uniform convergence
-- statement:
--   There exists $\delta_0>0$ for which the functions $g$, $\nabla g$, $\nabla^2g$, $g^{(M)}$, $\nabla g^{(M)}$, $\nabla^2g^{(M)}$ are all uniformly bounded over $\theta\in\mathbb R^l$, $\Lambda_\theta-\Lambda<\delta_0$ and $M>1$. Moreover $g^{(M)}(\theta,\Lambda)\uparrow g(\theta,\Lambda)$ and $\nabla g^{(M)}(\theta,\Lambda)\to\nabla g(\theta,\Lambda)$ as $M\uparrow\infty$, uniformly over $\theta\in\mathbb R^l$ and $\Lambda_\theta-\Lambda<\delta_0$. Here $\nabla$ is the full gradient in $(\theta,\Lambda)$.
--
--   These bounds make the Taylor expansions in the proof of Theorem 1 uniform.
--
--   Differences from the source:
--   - reading: no assumptions named in the statement → Assumptions 1 to 3; reason: the proofs in App. E cite them (Lemma 14's proof, p.40) and they are the standing assumptions of Theorem 1
--   - reading: bounded functions and bounded derivatives in Assumptions 2 and 3 → bounds uniform in θ, with no continuity of the second derivative; reason: Lemma 12's proof and Lemma 17 need uniform bounds; the page says twice differentiable, not C²
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
--   - reading: g^(M)(θ, Λ) ↑ g(θ, Λ) as M ↑ ∞ uniformly → g^(M) nondecreasing in M and ≤ g on the region, and uniform convergence with M₀ independent of θ and Λ; reason: this is the meaning of the arrow; the proof notes g^(M) < g, and G^(M) is nondecreasing in M
--   - reading: ∇g^(M)(θ, Λ) ↑ ∇g(θ, Λ) → uniform convergence of the vectors; reason: a vector has no monotone order here, and the proof shows uniform convergence
--   - encoding: the functions are uniformly bounded → the functions are finite and differentiable on the region, with one bound B; reason: this excludes the junk values of toReal and fderiv
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Lemma 17, p.42

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model
open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Lemma 17** (arXiv:2202.04157v2, p.42). There is `δ₀ > 0` such that `g`, `∇g`, `∇²g`, `g^(M)`,
`∇g^(M)`, `∇²g^(M)` (full gradients in `(θ, Λ)`) exist and are uniformly bounded over `θ ∈ ℝ^l`,
`Λ_θ - Λ < δ₀`, and `M > 1`. Moreover `g^(M) ↑ g` and `∇g^(M) → ∇g` as `M ↑ ∞`, uniformly over
`θ ∈ ℝ^l` and `Λ_θ - Λ < δ₀`. -/
theorem lemma_17 {X : Type*} [Fintype X] [DecidableEq X] {l : ℕ} (m : Model X l)
    (hm : m.IsValid) (h1 : m.Assumption1) (h2 : m.Assumption2) (h3 : m.Assumption3) :
    ∃ δ₀ > 0,
      (∃ B : ℝ, ∀ θ Λ, m.riskCost θ - Λ < δ₀ →
        (m.g θ Λ < ⊤ ∧
          DifferentiableAt ℝ m.gReal (θ, Λ) ∧
          DifferentiableAt ℝ (fderiv ℝ m.gReal) (θ, Λ) ∧
          |m.gReal (θ, Λ)| ≤ B ∧ ‖fderiv ℝ m.gReal (θ, Λ)‖ ≤ B ∧
          ‖fderiv ℝ (fderiv ℝ m.gReal) (θ, Λ)‖ ≤ B) ∧
        ∀ M, 1 < M →
          m.gTrunc M θ Λ < ⊤ ∧
          DifferentiableAt ℝ (m.gTruncReal M) (θ, Λ) ∧
          DifferentiableAt ℝ (fderiv ℝ (m.gTruncReal M)) (θ, Λ) ∧
          |m.gTruncReal M (θ, Λ)| ≤ B ∧ ‖fderiv ℝ (m.gTruncReal M) (θ, Λ)‖ ≤ B ∧
          ‖fderiv ℝ (fderiv ℝ (m.gTruncReal M)) (θ, Λ)‖ ≤ B) ∧
      (∀ M M', 1 < M → M ≤ M' → ∀ θ Λ, m.riskCost θ - Λ < δ₀ →
        m.gTruncReal M (θ, Λ) ≤ m.gTruncReal M' (θ, Λ) ∧
          m.gTruncReal M' (θ, Λ) ≤ m.gReal (θ, Λ)) ∧
      ∀ ε > 0, ∃ M₀ > 1, ∀ M ≥ M₀, ∀ θ Λ, m.riskCost θ - Λ < δ₀ →
        |m.gReal (θ, Λ) - m.gTruncReal M (θ, Λ)| < ε ∧
          ‖fderiv ℝ m.gReal (θ, Λ) - fderiv ℝ (m.gTruncReal M) (θ, Λ)‖ < ε := by sorry

end RiskExpPG
