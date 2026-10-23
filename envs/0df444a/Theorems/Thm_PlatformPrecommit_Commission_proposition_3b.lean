-- Prove2me | Theorems.Thm_PlatformPrecommit_Commission_proposition_3b
-- name    : PlatformPrecommit.Commission.proposition_3b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:14.952069+00:00
-- url     : https://prove2.me/theorems/27d861ea-45fe-497b-b258-249acfee89e3
-- title:
--   Proposition 3(b), p. 17 — commission precommitment versus no commitment
-- statement:
--   Let $\Omega>0$, with demand competition intensity $\gamma$ and supply competition intensity $\beta$ in $[0,1)$. For every such parameter pair, a symmetric selected subgame-perfect equilibrium of commission precommitment and a positive-profit Nash equilibrium of no commitment exist. The platform ranking of Definition 1 satisfies:
--
--   1. If $\gamma\geq\beta$, then $C\succeq P$.
--   2. For every $\beta\in(0,1)$, there is a threshold $\gamma_0\in(0,\beta]$ such that $C\succeq P$ whenever $0\leq\gamma<\gamma_0$.
--   3. For every $\beta\in[0,1)$, there is a $\delta>0$ such that $P\succeq C$ whenever $0\leq\gamma\leq\beta$ and $\beta-\delta<\gamma$.
--
--   The ranking compares each platform's equilibrium price, profit, wage, and matching quantity. It identifies when committing to a pay-out ratio improves the platforms' outcomes relative to choosing price and wage at once.
--
--   **Formalization Note** The two threshold clauses make the paper's “$\gamma\ll\beta$” and “sufficiently close to $\beta$” precise without choosing an unprinted numerical threshold. Both rankings include $\gamma=\beta$. Equilibrium existence is included to prevent vacuity; the commission SPE uses positive-profit subgame selection.
-- source:
--   Hu, Liu, Precommitments in Two-Sided Market Competition, submitted manuscript (SSRN 3734828; TSpace), p. 17, Proposition 3(b)(i)–(ii); p. 16, Definition 1

import Mathlib
import Definitions.Def_PlatformPrecommit_Commission_Setting

namespace PlatformPrecommit.Commission

/-- Proposition 3(b): commission precommitment versus no commitment. -/
theorem proposition_3b (Ω : ℝ) (hΩ : 0 < Ω) :
    (∀ β γ, (⟨Ω, β, γ⟩ : Model).Standing →
      (∃ α σ, IsCSPE ⟨Ω, β, γ⟩ α σ ∧ Symmetric α) ∧
      (∃ pw, IsPNE ⟨Ω, β, γ⟩ pw ∧ ∀ i, 0 < profP ⟨Ω, β, γ⟩ pw i)) ∧
    (∀ β γ, (⟨Ω, β, γ⟩ : Model).Standing → β ≤ γ →
      CPrefP ⟨Ω, β, γ⟩) ∧
    (∀ β, 0 < β → β < 1 → ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ β ∧
      ∀ γ, 0 ≤ γ → γ < γ₀ → CPrefP ⟨Ω, β, γ⟩) ∧
    (∀ β, 0 ≤ β → β < 1 → ∃ δ : ℝ, 0 < δ ∧
      ∀ γ, 0 ≤ γ → γ ≤ β → β - δ < γ → PPrefC ⟨Ω, β, γ⟩) := by sorry

end PlatformPrecommit.Commission
