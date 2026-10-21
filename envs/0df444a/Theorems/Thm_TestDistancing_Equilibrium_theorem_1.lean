-- Prove2me | Theorems.Thm_TestDistancing_Equilibrium_theorem_1
-- name    : TestDistancing.Equilibrium.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:10.092523+00:00
-- url     : https://prove2.me/theorems/665a3ba5-078e-496f-aba7-8e0d10eca65a
-- title:
--   Theorem 1 — non-monotone effect of testing in symmetric equilibrium, with continuity at region boundaries
-- statement:
--   Under the standing assumptions there is a positive integer $M$ such that, for every $n\ge M$, every testing policy has a symmetric equilibrium. Compare two coordinatewise ordered policies $\alpha\le\alpha'$ within the interior of the same region, and any symmetric equilibria at those policies. In $A_1$ and $A_3$, every agent's equilibrium infection probability weakly decreases. In $A_2$, when the policies differ, each low-value agent's probability strictly increases. In $A_4$, each high-value agent's probability weakly increases, strictly if $\alpha_H<\alpha'_H$; each inactive low-value agent has probability $1/n$ at both policies.
--
--   $$A_1,A_3:\ P_i^{\mathrm{eq}}(\alpha')\le P_i^{\mathrm{eq}}(\alpha);\qquad A_2:\ P_l^{\mathrm{eq}}(\alpha)<P_l^{\mathrm{eq}}(\alpha');\qquad A_4:\ P_h^{\mathrm{eq}}(\alpha)\le P_h^{\mathrm{eq}}(\alpha').$$
--
--   Finally, at every policy in $[0,1]^2$ on the boundary of one of $A_1,\dots,A_4$ (other than the degenerate $p=0$, $\alpha_L=1$), each agent's equilibrium infection probability is continuous in the policy: for every $\varepsilon>0$ there is $\delta>0$ such that any symmetric equilibrium at any policy within distance $\delta$ gives an infection probability within $\varepsilon$.
--
--   **Formalization Note** The high-type constancy clause in part (b) is false in the finite model and is omitted. The continuity sentence excludes the policy $p=0$, $\alpha_L=1$, where the equilibrium is not unique (see Proposition 2) and continuity fails. High types are the first $\lceil r_H n\rceil$ agents, and symmetric strategies mix on $\{0,1\}$. The existence clause prevents vacuity.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, pp. 13–14 (PDF 15–16), Theorem 1(a)–(d) and its closing continuity sentence

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Model

namespace TestDistancing.Equilibrium

/-- Theorem 1 (a)–(d) and the closing continuity sentence. Part (b)'s clause that high-value
agents' infection is unchanged is omitted (false at finite `n`). The continuity clause excludes
the degenerate policy `p = 0, α_L = 1`, at which equilibrium is not unique (see Proposition 2). -/
theorem theorem_1 (P : Params) (hP : P.Standing) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n →
      (∀ α ∈ PolicySquare, ∃ γ : ℝ × ℝ, IsSymEq P n γ α) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A1 P n) → α' ∈ interior (A1 P n) →
        PolicyLe α α' → IsSymEq P n γ α → IsSymEq P n γ' α' →
        ∀ i : Fin n, eqInf P γ' α' i ≤ eqInf P γ α i) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A2 P n) → α' ∈ interior (A2 P n) →
        PolicyLe α α' → α ≠ α' →
        IsSymEq P n γ α → IsSymEq P n γ' α' →
        ∀ l : Fin n, ¬ IsHigh P l → eqInf P γ α l < eqInf P γ' α' l) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A3 P n) → α' ∈ interior (A3 P n) →
        PolicyLe α α' → IsSymEq P n γ α → IsSymEq P n γ' α' →
        ∀ i : Fin n, eqInf P γ' α' i ≤ eqInf P γ α i) ∧
      (∀ (α α' γ γ' : ℝ × ℝ),
        α ∈ interior (A4 P n) → α' ∈ interior (A4 P n) →
        PolicyLe α α' → IsSymEq P n γ α → IsSymEq P n γ' α' →
        (∀ h : Fin n, IsHigh P h →
          eqInf P γ α h ≤ eqInf P γ' α' h ∧
          (α.2 < α'.2 → eqInf P γ α h < eqInf P γ' α' h)) ∧
        (∀ l : Fin n, ¬ IsHigh P l →
          eqInf P γ α l = (1 : ℝ) / n ∧
          eqInf P γ' α' l = (1 : ℝ) / n)) ∧
      (∀ α ∈ PolicySquare,
        (α ∈ frontier (A1 P n) ∨ α ∈ frontier (A2 P n) ∨
          α ∈ frontier (A3 P n) ∨ α ∈ frontier (A4 P n)) →
        (P.p = 0 → α.1 < 1) →
        ∀ γ : ℝ × ℝ, IsSymEq P n γ α → ∀ (i : Fin n) (ε : ℝ), 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ ∀ α' ∈ PolicySquare, dist α' α < δ →
            ∀ γ' : ℝ × ℝ, IsSymEq P n γ' α' →
              |eqInf P γ' α' i - eqInf P γ α i| < ε) := by sorry

end TestDistancing.Equilibrium
