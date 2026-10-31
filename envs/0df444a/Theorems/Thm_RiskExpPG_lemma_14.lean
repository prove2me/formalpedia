-- Prove2me | Theorems.Thm_RiskExpPG_lemma_14
-- name    : RiskExpPG.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:29.621279+00:00
-- url     : https://prove2.me/theorems/a87f04f2-8c9e-4064-94e7-821ab999881d
-- title:
--   Lemma 14 — gradient and $\Lambda$-derivative of $g$ (corrected: the twisted forms carry $e^{(\Lambda_\theta-\Lambda)\tau_{x^*}}$)
-- statement:
--   If $g(\theta,\Lambda)<\infty$, then $\nabla g(\theta,\Lambda)$ exists, and
--   $$\nabla_\theta g(\theta,\Lambda)=E^\theta_{\Phi_0=x^*}\Big[\sum_{i=0}^{\tau_{x^*}-1}\big(\alpha\nabla_\theta C_\theta(\Phi_i)+L_\theta(\Phi_i,\Phi_{i+1})\big)\exp\Big(\sum_{i=0}^{\tau_{x^*}-1}(\alpha C_\theta(\Phi_i)-\Lambda)\Big)\Big]$$
--   $$=\check E^\theta_{\check\Phi_0=x^*}\Big[e^{(\Lambda_\theta-\Lambda)\tau_{x^*}}\sum_{i=0}^{\tau_{x^*}-1}\big(\alpha\nabla_\theta C_\theta(\check\Phi_i)+L_\theta(\check\Phi_i,\check\Phi_{i+1})\big)\Big],$$
--   $$\frac{\mathrm dg(\theta,\Lambda)}{\mathrm d\Lambda}=-E^\theta_{\Phi_0=x^*}\Big[\tau_{x^*}\exp\Big(\sum_{i=0}^{\tau_{x^*}-1}(\alpha C_\theta(\Phi_i)-\Lambda)\Big)\Big]=-\check E^\theta_{\check\Phi_0=x^*}\big[\tau_{x^*}e^{(\Lambda_\theta-\Lambda)\tau_{x^*}}\big].$$
--
--   At $\Lambda=\Lambda_\theta$ the formulas give the risk-sensitive policy gradient of Eq. (7) through the implicit function theorem.
--
--   Differences from the source:
--   - correction: the twisted forms Ě[Σ(α∇C + L)] and −Ě[τ] for every (θ, Λ) with g(θ, Λ) < ∞ → both twisted forms carry the factor e^{(Λ_θ−Λ)τ}; reason: they hold as printed only at Λ = Λ_θ. Counterexample: two states, all entries 1/2, C ≡ 0, α = 1, L ≡ 0, Λ = 1: Λ_θ = 0, Ě = E, dg/dΛ = −E[τ e^{−τ}] ≈ −0.276, while the printed −Ě[τ] = −2. Eq. (23) on the same page carries the factor
--   - reading: no assumptions named in the statement → Assumptions 1 to 3; reason: the proofs in App. E cite them (Lemma 14's proof, p.40) and they are the standing assumptions of Theorem 1
--   - reading: bounded functions and bounded derivatives in Assumptions 2 and 3 → bounds uniform in θ, with no continuity of the second derivative; reason: Lemma 12's proof and Lemma 17 need uniform bounds; the page says twice differentiable, not C²
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
--   - encoding: ∇g(θ, Λ) exists, with the formulas for ∇_θ g and dg/dΛ → DifferentiableAt on ℝ^{l+1}, HasGradientAt, HasDerivAt, and the summability of each expectation; reason: this states existence and value together, and keeps the real sum away from its junk value
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Lemma 14, p.40

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model
open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Lemma 14** (arXiv:2202.04157v2, p.40), with the twisted forms corrected. If `g(θ, Λ) < ∞`, then
`g` is differentiable at `(θ, Λ)`, and
`∇_θ g(θ, Λ) = E^θ[Σ_{i<τ} (α∇_θ C_θ(Φᵢ) + L_θ(Φᵢ, Φᵢ₊₁)) exp(Σ_{i<τ} (α C_θ(Φᵢ) - Λ))]
  = Ě^θ[e^{(Λ_θ - Λ)τ} Σ_{i<τ} (α∇_θ C_θ(Φ̌ᵢ) + L_θ(Φ̌ᵢ, Φ̌ᵢ₊₁))]`,
`dg(θ, Λ)/dΛ = -E^θ[τ exp(Σ_{i<τ} (α C_θ(Φᵢ) - Λ))] = -Ě^θ[τ e^{(Λ_θ - Λ)τ}]`.

**Formalization Note** The page omits the factor `e^{(Λ_θ - Λ)τ}` in the twisted forms, which are
right only at `Λ = Λ_θ`. The proof on the page and its Eq. (23) carry the factor. -/
theorem lemma_14 {X : Type*} [Fintype X] [DecidableEq X] {l : ℕ} (m : Model X l)
    (hm : m.IsValid) (h1 : m.Assumption1) (h2 : m.Assumption2) (h3 : m.Assumption3)
    (θ : Param l) (Λ : ℝ) (hg : m.g θ Λ < ⊤) :
    DifferentiableAt ℝ m.gReal (θ, Λ) ∧
    excursionSummable (m.P θ) m.xstar m.xstar (fun e => m.H θ Λ e • m.score θ e) ∧
    HasGradientAt (fun θ' => m.gReal (θ', Λ))
      (excursionMean (m.P θ) m.xstar m.xstar fun e => m.H θ Λ e • m.score θ e) θ ∧
    excursionSummable (m.twisted θ) m.xstar m.xstar
      (fun e => Real.exp ((m.riskCost θ - Λ) * returnTime e) • m.score θ e) ∧
    excursionMean (m.P θ) m.xstar m.xstar (fun e => m.H θ Λ e • m.score θ e) =
      excursionMean (m.twisted θ) m.xstar m.xstar
        (fun e => Real.exp ((m.riskCost θ - Λ) * returnTime e) • m.score θ e) ∧
    excursionSummable (m.P θ) m.xstar m.xstar (fun e => (returnTime e : ℝ) * m.H θ Λ e) ∧
    HasDerivAt (fun Λ' => m.gReal (θ, Λ'))
      (-excursionMean (m.P θ) m.xstar m.xstar fun e => (returnTime e : ℝ) * m.H θ Λ e) Λ ∧
    excursionSummable (m.twisted θ) m.xstar m.xstar
      (fun e => (returnTime e : ℝ) * Real.exp ((m.riskCost θ - Λ) * returnTime e)) ∧
    excursionMean (m.P θ) m.xstar m.xstar (fun e => (returnTime e : ℝ) * m.H θ Λ e) =
      excursionMean (m.twisted θ) m.xstar m.xstar
        (fun e => (returnTime e : ℝ) * Real.exp ((m.riskCost θ - Λ) * returnTime e)) := by sorry

end RiskExpPG
