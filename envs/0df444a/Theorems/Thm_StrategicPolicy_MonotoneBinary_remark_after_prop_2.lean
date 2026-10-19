-- Prove2me | Theorems.Thm_StrategicPolicy_MonotoneBinary_remark_after_prop_2
-- name    : StrategicPolicy.MonotoneBinary.remark_after_prop_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:40.976229+00:00
-- url     : https://prove2.me/theorems/6d40bba6-b899-464e-a745-af606306e0bb
-- title:
--   §4, p. 6 — outcome monotonic policy induces a non-worsening response
-- statement:
--   Fix the finite strategic decision model, an outcome monotonic cost, and a policy $\pi\in[0,1]^m$ that is outcome monotonic. If $r_\pi(i)$ is the best response of an individual initially at $x_i$, then
--
--   $$q_i\le q_{r_\pi(i)}\qquad\text{for every }i.$$
--
--   This is the observation following Proposition 2: a monotonic policy never makes a lower-outcome destination the selected best response.
--
--   **Formalization Note** The cost assumption includes the paper's two §4 equivalences for distinct indices. The standing model assumes free staying, strictly ordered outcomes, and the tie rule in (5).
-- source:
--   Tsirtsis et al., Optimal Decision Making Under Strategic Behavior, arXiv:1905.09239v5, p. 6, §4, remark after Proposition 2

import Mathlib
import Definitions.Def_StrategicPolicy_MonotoneBinary_Setting

namespace StrategicPolicy.MonotoneBinary

variable {m : ℕ}

theorem remark_after_prop_2 [NeZero m]
    (p q : Fin m → ℝ) (γ : ℝ) (c : Fin m → Fin m → ℝ)
    (hstanding : Standing p q γ c) (hcost : OMCost q c)
    (π : Fin m → ℝ) (hπ : π ∈ Policies m) (hmono : OMPolicy q π) :
    ∀ i, q i ≤ q (br c q π i) := by sorry

end StrategicPolicy.MonotoneBinary
