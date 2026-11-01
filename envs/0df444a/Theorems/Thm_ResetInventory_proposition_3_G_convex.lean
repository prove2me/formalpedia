-- Prove2me | Theorems.Thm_ResetInventory_proposition_3_G_convex
-- name    : ResetInventory.proposition_3_G_convex
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:43.468979+00:00
-- url     : https://prove2.me/theorems/99908c4b-f4c8-41b2-b54f-f2f66784f1ef
-- title:
--   Proposition 3 — $G(\cdot,t)$ is continuous and convex
-- statement:
--   **Proposition 3.** Let A2 hold at the age $t$ (constants $\kappa_t\ge0$, $m_t>0$), let the demand density satisfy A5 (constants $L,P$), let $c_{\max}\ge0$, $c\ge0$ and $0\le\gamma<1$, and let $V=J(\cdot,t+1)$ be continuous and piecewise $C^1$ on $[0,c_{\max}]$ with derivative bounded by $M=M_{t+1}$ (Assumption T, without its Lipschitz requirement). If
--   $$
--   0\le\gamma\le\frac{m_t}{(Lc_{\max}+P)\,M_{t+1}},
--   $$
--   then the function
--   $$
--   G(z,t)=c\,z+H(z,t)+\gamma\,\mathbb E\big(J((z-w)^+,t+1)\big)
--   $$
--   is continuous and convex on $z\in[0,c_{\max}]$.
--
--   The expected cost-to-go is not convex: the reset option makes the value function a minimum of convex and concave pieces. A small enough discount factor still makes the sum convex, because the strong convexity of $H$ dominates the bounded curvature that Proposition 2 gives the discounted cost-to-go.
--
--   Differences from the source:
--   - generalization: if A1–A5 and AT hold → A2 at t, A5, c_max ≥ 0, c ≥ 0 and 0 ≤ γ < 1 (A3 not assumed); reason: A3 is not used; A1 and A4 are built into the model; every instance of the source satisfies the hypotheses
--   - generalization: AT: J(·,t+1) is piecewise differentiable on a partition of [0, c_max], each piece's derivative bounded by M_{t+1} and Lipschitz continuous → PiecewiseC1: continuous, piecewise C¹ on a partition of [0, c_max] with derivative bounded by M_{t+1}, no Lipschitz requirement on the derivatives; reason: the proofs use only the continuity of the pieces and their derivatives and the bound M_{t+1}; every function satisfying AT satisfies PiecewiseC1
--   - generalization: the value function J(·,t+1) → any function V satisfying PiecewiseC1; reason: the proposition uses only the stated properties of J(·,t+1); the paper's J(·,t+1) is an instance
--   - encoding: 0 ≤ γ ≤ m_t/((L c_max + P) M_{t+1}) → 0 ≤ γ and γ · ((L c_max + P) · M_{t+1}) ≤ m_t; reason: equal when M_{t+1} > 0; at M_{t+1} = 0 the paper's quotient is undefined and imposes no bound, while Lean's x/0 = 0 would force γ = 0
--   - encoding: derivatives ∂ₓH, ∂ₓₓH, ∂ₓR, ∂_zJ_i and the derivatives in the conclusions → derivatives within [0, c_max] (one-sided at 0 and c_max), with the derivative functions named explicitly; reason: at interior points this is the ordinary derivative; at the ends the paper's functions live on [0, c_max], and its retail example (∂ₓₓH = (p+q)f with a jump of f at 0) needs one-sided derivatives
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Proposition 3, p.18; proof, pp.31–32

import Mathlib
import Definitions.Def_ResetInventory_A2
import Definitions.Def_ResetInventory_A5
import Definitions.Def_ResetInventory_PiecewiseC1
import Definitions.Def_ResetInventory_costG

namespace ResetInventory

/-- **Proposition 3** of Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, p.18. If A1–A5 and AT
hold, then the function `G(z, t) = c z + H(z, t) + γ E(J((z − w)⁺, t + 1))` is continuous and
convex on `z ∈ [0, c_max]` for all fixed `γ` such that `0 ≤ γ ≤ m_t / ((L c_max + P) M_{t+1})`.

Here `V = J(·, t + 1)` and `M = M_{t+1}`.

**Formalization Note** AT is `PiecewiseC1` (without its Lipschitz requirement on the pieces'
derivatives). The bound on `γ` is multiplicative, `γ (L c_max + P) M ≤ m_t` (equal to the paper's
when `M > 0`; at `M = 0` the paper's quotient is undefined and means no bound). The assumptions used
are A2 at `t`, A5, `c_max ≥ 0`, `c ≥ 0` and `0 ≤ γ < 1`; A1 and A4 are built into the model, and A3
is not used. -/
theorem proposition_3_G_convex (mdl : ResetModel) (κ m : ℕ → ℝ) (L P M : ℝ) (t : ℕ)
    (V : ℝ → ℝ)
    (hcmax : 0 ≤ mdl.cmax) (hc : 0 ≤ mdl.c) (hγ0 : 0 ≤ mdl.γ) (hγ1 : mdl.γ < 1)
    (hA2 : A2 mdl κ m t) (hA5 : A5 mdl.f L P) (hV : PiecewiseC1 mdl.cmax M V)
    (hγ : mdl.γ * ((L * mdl.cmax + P) * M) ≤ m t) :
    ContinuousOn (costG mdl V t) (Set.Icc 0 mdl.cmax) ∧
      ConvexOn ℝ (Set.Icc 0 mdl.cmax) (costG mdl V t) := by sorry

end ResetInventory
