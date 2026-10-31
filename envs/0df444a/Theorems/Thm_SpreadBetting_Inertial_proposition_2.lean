-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_proposition_2
-- name    : SpreadBetting.Inertial.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:23.182617+00:00
-- url     : https://prove2.me/theorems/8b0bc7db-faed-415c-8f64-e8e16870e2d6
-- title:
--   Proposition 2, p. 15 — every ρ : ℤ₊ → (0, ½ − α) determines a unique pricing function s̃ : ℤ → [m₀, m₁] and extension of ρ with F₀(s̃(−z)) = ½ + ρ(z), F₁(s̃(z)) = ½ − ρ(z)
-- statement:
--   Let the market satisfy the standing assumptions and let $\rho : \mathbb Z_+ \to (0, \tfrac12 - \alpha)$, where $\alpha = F_1(m_0)$. Let $\tilde s$ be the pricing function (4.3) and extend $\rho$ to $\mathbb Z$ by (E.1). Then for every $z \in \mathbb Z$,
--   $$
--   \tilde s(z) \in [m_0, m_1],\qquad F_0(\tilde s(-z)) = \tfrac12 + \rho(z),\qquad F_1(\tilde s(z)) = \tfrac12 - \rho(z). \tag{4.2}
--   $$
--   Moreover the pair is unique: any $s' : \mathbb Z \to [m_0, m_1]$ and $\rho' : \mathbb Z \to \mathbb R$ with $\rho' = \rho$ on $\mathbb Z_+$ that satisfy (4.2) coincide with $\tilde s$ and the extension (E.1).
--
--   This is the residual-probability representation of the inertial policy: the distance of the spread line from each median is encoded by a single number $\rho(z)$.
--
--   **Formalization Note** $F_i^{-1}$ is the generalized inverse $\inf\{x : p \le F_i(x)\}$; the statement certifies that it is the true inverse at the points used.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 15, Proposition 2, (4.2)–(4.3); p. 45, (E.1)

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem proposition_2 (M : Market) (hM : M.Standing) (ρp : ℕ → ℝ)
    (hρ : ∀ z : ℕ, 1 ≤ z → ρp z ∈ Set.Ioo 0 (1 / 2 - alpha M)) :
    (∀ z : ℤ, sTilde M ρp z ∈ Set.Icc M.m0 M.m1 ∧
      F M 0 (sTilde M ρp (-z)) = 1 / 2 + rhoExt M ρp z ∧
      F M 1 (sTilde M ρp z) = 1 / 2 - rhoExt M ρp z) ∧
    (∀ s' ρ' : ℤ → ℝ, (∀ z, s' z ∈ Set.Icc M.m0 M.m1) →
      (∀ z : ℤ, 0 < z → ρ' z = ρp z.toNat) →
      (∀ z : ℤ, F M 0 (s' (-z)) = 1 / 2 + ρ' z ∧ F M 1 (s' z) = 1 / 2 - ρ' z) →
      s' = sTilde M ρp ∧ ρ' = rhoExt M ρp) := by sorry

end SpreadBetting.Inertial
