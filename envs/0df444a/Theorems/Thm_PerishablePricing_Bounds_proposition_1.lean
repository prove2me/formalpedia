-- Prove2me | Theorems.Thm_PerishablePricing_Bounds_proposition_1
-- name    : PerishablePricing.Bounds.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:13.66621+00:00
-- url     : https://prove2.me/theorems/8fd903a2-bc93-4d5a-a83d-e1513a044462
-- title:
--   Proposition 1 (Minimum Disposal), p. 292 (k = 0) — if θ ≥ h⁺/(1 − γ), depleting d_t ∨ s₁ is optimal
-- statement:
--   Consider the backlogging model with lifetime $l\ge 2$ and zero lead time, under the standing assumptions of §3 and the assumption $c\le h^-/(1-\gamma)$ of §4. Suppose that $\gamma<1$ and
--
--   $$\theta\ \ge\ \frac{h^+}{1-\gamma}.$$
--
--   Then in every period the minimal depletion $a=d_t\vee s_1$ is optimal in (5): for every state $s\in\mathcal S$, every order-up-to level $s_l\ge s_{l-1}$, every $d$ and every realized noise $\varepsilon$, with $d_t=d+\varepsilon$,
--
--   $$\varphi_t(s,s_l,d,\ d_t\vee s_1\mid\varepsilon)=g_t(s,s_l,d\mid\varepsilon).$$
--
--   When disposal is at least as expensive as holding a unit forever, the seller only disposes of inventory that is expiring.
--
--   **Formalization Note.** The paper's "the optimal depletion decision is always equal to $d_t\vee s_1$" is formalized as optimality of $d_t\vee s_1$; uniqueness is not claimed, since at $\theta=h^+/(1-\gamma)$ other depletions can tie. The hypothesis $\theta\ge h^+/(1-\gamma)$ is stated as $h^+\le(1-\gamma)\theta$ together with $\gamma<1$, which the quotient requires. The assumption $(1-\gamma)c\le h^-$ is the standing assumption of §4, in multiplied form. Time is counted in periods to go (continuation `f n`).
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Proposition 1, p. 292, with lead time k = 0

import Mathlib
import Definitions.Def_PerishablePricing_Bounds_Model

namespace PerishablePricing.Bounds

/-- Proposition 1 (Minimum Disposal, p. 292) at lead time `k = 0`: if `θ ≥ h⁺/(1 − γ)` (with
`γ < 1`), then for every period the depletion `a = d_t ∨ s₁` attains the maximum in (5):
`φ_t(s, s_l, d, d_t ∨ s₁ | ε) = g_t(s, s_l, d | ε)` for every state `s ∈ 𝒮`, every order-up-to level
`s_l ≥ s_{l−1}`, every `d` and every noise value `ε`, where `d_t = d + ε`. -/
theorem proposition_1 (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (sl : ℝ) (hsl : sLast s ≤ sl) (d ε : ℝ) :
    M.phi (M.f n) s sl d (max (d + ε) (sFirst s)) ε = M.g (M.f n) s sl d ε := by sorry

end PerishablePricing.Bounds
