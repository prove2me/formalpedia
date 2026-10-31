-- Prove2me | Theorems.Thm_SpreadBetting_Inertial_lemma_H_1
-- name    : SpreadBetting.Inertial.lemma_H_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:12.173786+00:00
-- url     : https://prove2.me/theorems/0d25039d-a56f-4a6e-bde8-e43238929025
-- title:
--   Lemma H.1, p. 60 — for r ∈ (0, r̄), ρ(z) = 1/(r₀ + rz) is regular and slowly vanishing
-- statement:
--   Let the market satisfy the standing assumptions and $r \in (0, \bar r)$. Then the sequence $\rho = \{\rho(z) = 1/(r_0 + rz), z \in \mathbb Z_+\}$ is regular (Definition 3) and slowly vanishing (Definition 2): it takes values in $(0, \tfrac12 - \alpha)$, $\liminf_z z\rho(z) > \tfrac14$, $\rho(z) \to 0$, and $\rho(z)/\rho(z+1) = 1 + A/z + o(1/z)$ for some $A \in \mathbb R \cup \{\pm\infty\}$.
--
--   This places the paper's policy inside the general family covered by Proposition K.2.
-- source:
--   Birge, Feng, Keskin & Schultz, SSRN 3283392 (version of April 14, 2020), p. 60, Lemma H.1; Definitions 2–3 pp. 27–28

import Mathlib
import Definitions.Def_SpreadBetting_Inertial_Model
import Definitions.Def_SpreadBetting_Inertial_Chain

namespace SpreadBetting.Inertial

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_H_1 (M : Market) (hM : M.Standing) (r : ℝ) (hr0 : 0 < r) (hr : r < rbar M) :
    SlowlyVanishing M (rhoIP M r) ∧ Regular (rhoIP M r) := by sorry

end SpreadBetting.Inertial
