-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_3
-- name    : SpreadBetting.Inertial.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:21.582857+00:00
-- url     : https://prove2.me/theorems/c1bbac23-e48a-4d24-a7e4-d3bd76b224cc
-- title:
--   Lemma 3, p. 21 — Bellman optimality (4.11): J̄ⁱ(z) is the max of the three one-step continuation values
-- statement:
--   Let the market satisfy the standing assumptions and $\rho(z) = 1/(r_0 + rz)$ with $r \in (0, \bar r)$. Then $\bar J^1$ and $\bar J^0$ of (4.8) satisfy, for all $z \in \mathbb Z$,
--   $$
--   \bar J^1(z) = \max\Big\{ j_1^+(z) + \bar J^1(z+1),\ j_1^-(z) + \bar J^1(z-1),\ \bar F_1(\tilde s(z))\bar J^1(z+1) + F_1(\tilde s(z))\bar J^1(z-1)\Big\},
--   $$
--   $$
--   \bar J^0(z) = \max\Big\{ j_0^+(z) + \bar J^0(z+1),\ j_0^-(z) + \bar J^0(z-1),\ \bar F_0(\tilde s(z))\bar J^0(z+1) + F_0(\tilde s(z))\bar J^0(z-1)\Big\}. \tag{4.11}
--   $$
--   The three terms are the informed bettor's profits from betting $+1$, betting $-1$ and waiting, so the informed bettor has no incentive to deviate from $\xi_i^*$.
--
--   **Formalization Note** $j_i^\pm(z)$ abbreviates $j_i^\pm(\tilde s(z))$. The "no incentive to deviate" sentence of the lemma is its Bellman equation, as the paper's "That is" says.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 21, Lemma 3, (4.11)

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_3 (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    let ρp := rhoIP M r
    (∀ z : ℤ, Jbar1 M ρp z = max (max (jPlusZ M ρp 1 z + Jbar1 M ρp (z + 1))
        (jMinusZ M ρp 1 z + Jbar1 M ρp (z - 1)))
      (Fbar M 1 (sTilde M ρp z) * Jbar1 M ρp (z + 1) + F M 1 (sTilde M ρp z) * Jbar1 M ρp (z - 1))) ∧
    (∀ z : ℤ, Jbar0 M ρp z = max (max (jPlusZ M ρp 0 z + Jbar0 M ρp (z + 1))
        (jMinusZ M ρp 0 z + Jbar0 M ρp (z - 1)))
      (Fbar M 0 (sTilde M ρp z) * Jbar0 M ρp (z + 1) + F M 0 (sTilde M ρp z) * Jbar0 M ρp (z - 1))) := by sorry

end SpreadBetting.Inertial
