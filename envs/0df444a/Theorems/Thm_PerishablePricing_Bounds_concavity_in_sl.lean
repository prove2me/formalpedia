-- Prove2me | Theorems.Thm_PerishablePricing_Bounds_concavity_in_sl
-- name    : PerishablePricing.Bounds.concavity_in_sl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:59.888965+00:00
-- url     : https://prove2.me/theorems/f4458df1-bef9-4774-9b2d-7f2a093f3d76
-- title:
--   Proof of Theorem 3, p. 295 — Π_t(s_l, d) and G_t(s, s_l, d) are concave in s_l
-- statement:
--   Consider the backlogging model with lifetime $l\ge 2$ and zero lead time, under the standing assumptions of §3, §4 and §6.1. For every period, every state $s\in\mathcal S$ and every expected demand $d\in\mathcal D$:
--
--   1. $s_l\mapsto\Pi_t(s_l,d)$ is concave on $\mathbb R$;
--   2. $s_l\mapsto G_t(s,s_l,d)$ is concave on the feasible half-line $s_l\ge s_{l-1}$.
--
--   Together with the two difference inequalities of the proof, concavity turns a comparison of increments into a comparison of maximizers.
--
--   **Formalization Note.** Time is counted in periods to go: $G_t$ is `G (f n)`. The concavity of $G_t$ in $s_l$ is a consequence of Theorem 1 (L♮-concavity of $g_t$), integrated over the noise.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, proof of Theorem 3, p. 295, 'By the concavity of Π_t(s_l, d) and G_t(s, s_l, d) in s_l'

import Mathlib
import Definitions.Def_PerishablePricing_Bounds_Myopic

namespace PerishablePricing.Bounds

/-- Proof of Theorem 3 (p. 295), "the concavity of `Π_t(s_l, d)` and `G_t(s, s_l, d)` in `s_l`"
(zero lead time, backlogging, `θ ≥ h⁺/(1 − γ)`): for every expected demand `d ∈ 𝒟`,
`s_l ↦ Π_t(s_l, d)` is concave on `ℝ`, and for every state `s ∈ 𝒮`,
`s_l ↦ G_t(s, s_l, d)` is concave on the feasible half-line `s_l ≥ s_{l−1}`. -/
theorem concavity_in_sl (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (d : ℝ) (hd : d ∈ Set.Icc M.dlo M.dhi) :
    ConcaveOn ℝ Set.univ (fun sl => M.Pi sl d) ∧
      ConcaveOn ℝ (Set.Ici (sLast s)) (fun sl => M.G (M.f n) s sl d) := by sorry

end PerishablePricing.Bounds
