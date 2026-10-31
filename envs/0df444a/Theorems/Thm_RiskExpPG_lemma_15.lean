-- Prove2me | Theorems.Thm_RiskExpPG_lemma_15
-- name    : RiskExpPG.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:26:39.277603+00:00
-- url     : https://prove2.me/theorems/95010c25-56f7-46cd-b4e5-cff31985f253
-- title:
--   Lemma 15 — $f^{(M)}=\nabla_\theta g^{(M)}$ and the sensitivity formula for $\Lambda^{(M)}_\theta$
-- statement:
--   For $M>1$ and any $(\theta,\Lambda)\in\mathbb R^{l+1}$, the expectation $f^{(M)}(\theta,\Lambda)$ exists and $f^{(M)}(\theta,\Lambda)=\nabla_\theta g^{(M)}(\theta,\Lambda)$. In particular,
--   $$f^{(M)}\big(\theta,\Lambda^{(M)}_\theta\big)=-\frac{\mathrm dg^{(M)}(\theta,\Lambda)}{\mathrm d\Lambda}\bigg|_{\Lambda=\Lambda^{(M)}_\theta}\nabla_\theta\Lambda^{(M)}_\theta.$$
--
--   So the expectation of the cycle statistic $F^{(M)}$ points in the direction of the gradient of the truncated cost.
--
--   Differences from the source:
--   - reading: no assumptions named in the statement → Assumptions 1 to 3; reason: the proofs in App. E cite them (Lemma 14's proof, p.40) and they are the standing assumptions of Theorem 1
--   - reading: bounded functions and bounded derivatives in Assumptions 2 and 3 → bounds uniform in θ, with no continuity of the second derivative; reason: Lemma 12's proof and Lemma 17 need uniform bounds; the page says twice differentiable, not C²
--   - reading: M with no lower bound in the statement → M > 1; reason: §5.2, p.8 defines g^(M), f^(M) and Λ^(M) only for M > 1
--   - encoding: expectations over the first return time τ_{x*} → sums over finite excursions, in ℝ≥0∞ or as a real sum with its summability asserted; reason: Assumption 1 makes τ_{x*} finite almost surely, so the values agree and +∞ stays representable
--   - encoding: f^(M) = ∇_θ g^(M), and the display with ∇_θ Λ^(M)_θ → HasGradientAt, summability of F^(M), and differentiability of Λ^(M) and of g^(M)(θ, ·); reason: this states existence and value together and excludes the junk value of gradient and deriv
-- source:
--   Moharrami, Murthy, Roy & Srikant, A Policy Gradient Algorithm for the Risk-Sensitive Exponential Cost MDP, arXiv:2202.04157v2, Lemma 15, p.41

import Mathlib
import Definitions.Def_RiskExpPG_Chain
import Definitions.Def_RiskExpPG_Model
open Filter Topology MeasureTheory
open scoped ENNReal

namespace RiskExpPG

/-- **Lemma 15** (arXiv:2202.04157v2, p.41). For `M > 1` and any `(θ, Λ)`, the expectation
`f^(M)(θ, Λ)` exists and equals `∇_θ g^(M)(θ, Λ)`. In particular
`f^(M)(θ, Λ^(M)_θ) = -(dg^(M)(θ, Λ)/dΛ |_{Λ = Λ^(M)_θ}) ∇_θ Λ^(M)_θ`, where `Λ^(M)` is differentiable
and `g^(M)(θ, ·)` is differentiable at `Λ^(M)_θ`. -/
theorem lemma_15 {X : Type*} [Fintype X] [DecidableEq X] {l : ℕ} (m : Model X l)
    (hm : m.IsValid) (h1 : m.Assumption1) (h2 : m.Assumption2) (h3 : m.Assumption3)
    (M : ℝ) (hM : 1 < M) :
    (∀ θ Λ, excursionSummable (m.P θ) m.xstar m.xstar (m.F M θ Λ) ∧
      HasGradientAt (fun θ' => m.gTruncReal M (θ', Λ)) (m.fTrunc M θ Λ) θ) ∧
    ∀ θ, DifferentiableAt ℝ (fun Λ' => m.gTruncReal M (θ, Λ')) (m.truncCost M θ) ∧
      DifferentiableAt ℝ (m.truncCost M) θ ∧
      m.fTrunc M θ (m.truncCost M θ) =
        (-deriv (fun Λ' => m.gTruncReal M (θ, Λ')) (m.truncCost M θ)) •
          gradient (m.truncCost M) θ := by sorry

end RiskExpPG
