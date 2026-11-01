-- Prove2me | Theorems.Thm_ResetInventory_proposition_6_value_function_form
-- name    : ResetInventory.proposition_6_value_function_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:48.128984+00:00
-- url     : https://prove2.me/theorems/73e5de21-5a3e-4487-8c75-6e051665205e
-- title:
--   Proposition 6 — form (28) of the value function and the bound $M_t$ (corrected: Lipschitz clause of the third piece conditional)
-- statement:
--   **Proposition 6 (corrected).** Under the hypotheses of Proposition 5, there are a constant $\varphi\in[0,c_{\max}]$ attaining $J_0=J(0,0)$ and, for each $t=0,\dots,k-1$, thresholds $0\le\sigma_t\le s_t\le\Sigma_t\le+\infty$ and $S_t\in[0,c_{\max}]$ (with $s_t\le S_t$ when $\sigma_t<s_t$) such that the four-threshold policy (23) attains the minimum in (22) at every $x\in[0,c_{\max}]$ and $J(x,t)$ has the form
--   $$
--   J(x,t)=\begin{cases}
--   J_0+\mathbb E(s(x,t,w)), & x\in[0,\sigma_t),\\
--   c(S_t-x)+K+H(S_t,t)+\gamma\,\mathbb E\big(J((S_t-w)^+,t+1)\big), & x\in[\sigma_t,s_t),\\
--   H(x,t)+\gamma\,\mathbb E\big(J((x-w)^+,t+1)\big), & x\in[s_t,\Sigma_t),\\
--   J_0+\mathbb E(s(x,t,w)), & x\ge\Sigma_t.
--   \end{cases}\tag{28}
--   $$
--   Furthermore, each piece has a continuous derivative on $[0,c_{\max}]$, and the derivative of each piece is absolutely bounded by
--   $$
--   M_t=\eta_t+c+\kappa_t+\frac{m_t}{Lc_{\max}+P}.
--   $$
--   The derivatives of the reset piece $J_0+\mathbb E(s(x,t,w))$ and of the order-up-to piece are Lipschitz. If in addition $\partial_xH(\cdot,t)$ is Lipschitz on $[0,c_{\max}]$, the derivative of the piece $H(x,t)+\gamma\,\mathbb E(J((x-w)^+,t+1))$ is Lipschitz too.
--
--   The paper states the last part as "each piece has a Lipschitz derivative" without the extra condition; for the third piece that is false in general (see below). The derivative bound $M_t$ is what Theorem 1 feeds back into Assumption T at the next age down.
--
--   Differences from the source:
--   - correction: each piece of (28) has a Lipschitz derivative → each piece has a derivative on [0, c_max] that is continuous and bounded by M_t; the derivatives of the reset piece and of the order-up-to piece are Lipschitz, and that of the piece H(x,t) + γE J((x−w)⁺,t+1) is Lipschitz if ∂ₓH(·,t) is Lipschitz on [0, c_max]; reason: false as printed: k = 1, c_max = 2, γ = 0, c = 1/2, K = 0, R ≡ 0, f(w) = (1 − |w − 1|)⁺, H(z,0) = (z−1)²/2 + εφ(z) with φ'' = Σ_{n≥2} n β(n⁴(z − 1 − 1/n)) (β a smooth bump) satisfies A1–A5 and (29) with ∂ₓₓH ≥ 1, but ∂ₓₓH(1 + 1/n, 0) ≥ εn is unbounded; a right-neighbourhood of x = 1 lies in the do-nothing region for every choice of thresholds, where J(x,0) = H(x,0) has a non-Lipschitz derivative (the appendix's 'Lipschitz because twice differentiable by A2', p.35, is the gap)
--   - generalization: the derivative of each piece (on its region of (28)) → the derivative claims for each piece formula on all of [0, c_max]; reason: the piece formulas are defined on all of [0, c_max]; the claim on [0, c_max] implies the claim on each region
--   - reading: J(x,t) has the form (28) with (s_t, S_t, σ_t, Σ_t) thresholds → the form (28) holds for the same thresholds for which the policy (23) attains the minimum in (22); reason: the proposition refers to the thresholds of Proposition 5's policy, whose structure 'implies that the value function J(x,t) takes the form (28)' (proof, p.34)
--   - generalization: AT: J(·,t+1) is piecewise differentiable on a partition of [0, c_max], each piece's derivative bounded by M_{t+1} and Lipschitz continuous → PiecewiseC1: continuous, piecewise C¹ on a partition of [0, c_max] with derivative bounded by M_{t+1}, no Lipschitz requirement on the derivatives; reason: the proofs use only the continuity of the pieces and their derivatives and the bound M_{t+1}; every function satisfying AT satisfies PiecewiseC1
--   - generalization: §2 setting: g ≥ 0 and s ≥ 0 continuous, s(ζ,t,w) ≡ 0 → no sign, continuity or s(ζ,·,·) ≡ 0 condition on H and R beyond A2 and A3; reason: the proofs never use these conditions (continuity of H and R follows from A2 and A3); every instance of the paper satisfies the remaining hypotheses
--   - reading: an optimal policy (for problem (2)) → for every solution J of the dynamic programming equations (22), the policy's action is feasible and its value equals J(x,t), i.e. it attains the minimum in (22); reason: the paper proves optimality with respect to (22) (p.14: 'the optimal fixed point policy π* … to (22)'); the link from (22) to (2) is Proposition 1, cited from Mintz et al. (2017) and not proved in the paper
--   - reading: states x ∈ ℝ₊ (A1), with AT on the domain [0, c_max] → every state, equation and conclusion on x ∈ [0, c_max]; reason: AT and the proofs of Propositions 5 and 6 work on [0, c_max]; from x ≤ c_max the dynamics stay in [0, c_max], and for x > c_max the order set U = [0, c_max − x] of A4 is empty
--   - encoding: thresholds (s_t, S_t, σ_t, Σ_t) defining the four intervals of (23) → ∃ σ_t ≤ s_t ≤ Σ_t in EReal with 0 ≤ σ_t, S_t ∈ [0, c_max], and s_t ≤ S_t when σ_t < s_t; reason: the paper's thresholds may be +∞ (p.33, Figure 6) and its four intervals must partition [0, ∞) for (23) to define a policy; S_t ≥ s_t makes the order S_t − x positive on [σ_t, s_t), as in the paper's construction s_t = s'_t ≤ S'_t
--   - encoding: 0 ≤ γ ≤ m_t/((L c_max + P) M_{t+1}) → 0 ≤ γ and γ · ((L c_max + P) · M_{t+1}) ≤ m_t; reason: equal when M_{t+1} > 0; at M_{t+1} = 0 the paper's quotient is undefined and imposes no bound, while Lean's x/0 = 0 would force γ = 0
--   - encoding: stage cost g(ξ,τ,u,w) and reset cost s(x,t,w), with E g = cu + K·1(u>0) + H(ξ+u,τ) (A2) and R = E s (A3) → the model carries c, K, H and R; reason: g and s enter (22) only through these expectations; same instances
--   - encoding: derivatives ∂ₓH, ∂ₓₓH, ∂ₓR, ∂_zJ_i and the derivatives in the conclusions → derivatives within [0, c_max] (one-sided at 0 and c_max), with the derivative functions named explicitly; reason: at interior points this is the ordinary derivative; at the ends the paper's functions live on [0, c_max], and its retail example (∂ₓₓH = (p+q)f with a jump of f at 0) needs one-sided derivatives
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Proposition 6, pp.20–21; proof, p.35

import Mathlib
import Definitions.Def_ResetInventory_A2
import Definitions.Def_ResetInventory_A3
import Definitions.Def_ResetInventory_A5
import Definitions.Def_ResetInventory_PiecewiseC1
import Definitions.Def_ResetInventory_IsDPSolution
import Definitions.Def_ResetInventory_policy
import Definitions.Def_ResetInventory_IsOptimalAction
import Definitions.Def_ResetInventory_form28
import Definitions.Def_ResetInventory_Mbound
import Definitions.Def_ResetInventory_PieceDerivBound
import Definitions.Def_ResetInventory_HDerivLipschitz

namespace ResetInventory

/-- **Proposition 6** of Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, pp.20–21, with its
Lipschitz clause corrected. Suppose `0 ≤ γ ≤ m_t / ((L c_max + P) M_{t+1})` for all
`t = 0, …, k − 1`. If A1–A5 and AT hold, then `J(x, t)` for `t = 0, …, k − 1` has the form (28)
with `(s_t, S_t, σ_t, Σ_t)` thresholds, and the derivative of each piece is absolutely bounded by
`M_t = η_t + c + κ_t + m_t / (L c_max + P)`.

Lean: for every solution `J` of (22), there is `ϕ ∈ [0, c_max]` attaining `J₀`, and for every
`t < k` there are the thresholds of Proposition 5 (ordered, the policy (23) attaining the minimum
of (22) at every `x ∈ [0, c_max]`) for which also `J(x, t)` equals the right side of (28) at every
`x ∈ [0, c_max]`, and each of the three piece functions `x ↦ J₀ + R(x, t)`,
`x ↦ c(S_t − x) + K + H(S_t, t) + γ E J((S_t − w)⁺, t + 1)` and
`x ↦ H(x, t) + γ E J((x − w)⁺, t + 1)` has on `[0, c_max]` a continuous derivative bounded in
absolute value by `M_t`; the derivatives of the first two are Lipschitz on `[0, c_max]`, and that
of the third is Lipschitz on `[0, c_max]` if `∂ₓH(·, t)` is.

**Formalization Note** Correction: the paper asserts that each piece has a Lipschitz derivative
unconditionally, which fails for the third piece when `∂ₓₓH(·, t)` is unbounded (Assumption 2
bounds it only from below); that piece's Lipschitz clause is therefore conditional on
`HDerivLipschitz mdl t`, and the other two pieces keep it unconditionally (`lipCond := True`). The
derivative
claims are stated for the piece formulas on all of `[0, c_max]`, not only on their regions. AT is
`PiecewiseC1` (without its Lipschitz requirement); the `γ` bound is multiplicative; thresholds as in
Proposition 5. -/
theorem proposition_6_value_function_form (mdl : ResetModel) (κ m η Lt : ℕ → ℝ) (L P : ℝ)
    (M : ℕ → ℝ)
    (hcmax : 0 ≤ mdl.cmax) (hc : 0 ≤ mdl.c) (hK : 0 ≤ mdl.K)
    (hγ0 : 0 ≤ mdl.γ) (hγ1 : mdl.γ < 1)
    (hA2 : ∀ t < mdl.k, A2 mdl κ m t) (hA3 : ∀ t < mdl.k, A3 mdl η Lt t)
    (hA5 : A5 mdl.f L P)
    (hγ : ∀ t < mdl.k, mdl.γ * ((L * mdl.cmax + P) * M (t + 1)) ≤ m t)
    (J : ℝ → ℕ → ℝ) (hJ : IsDPSolution mdl J)
    (hAT : ∀ t < mdl.k, PiecewiseC1 mdl.cmax (M (t + 1)) (fun y => J y (t + 1))) :
    ∃ ϕ ∈ Set.Icc 0 mdl.cmax, orderValue mdl J 0 0 ϕ = J 0 0 ∧
      ∀ t < mdl.k, ∃ (σ s Sg : EReal) (S : ℝ),
        0 ≤ σ ∧ σ ≤ s ∧ s ≤ Sg ∧ S ∈ Set.Icc 0 mdl.cmax ∧ (σ < s → s ≤ (S : EReal)) ∧
        (∀ x ∈ Set.Icc 0 mdl.cmax,
          IsOptimalAction mdl J x t (policy σ s Sg S ϕ x) ∧
          J x t = form28 mdl J σ s Sg S x t) ∧
        PieceDerivBound mdl.cmax (Mbound mdl κ m η L P t) True
          (fun x => J 0 0 + mdl.R x t) ∧
        PieceDerivBound mdl.cmax (Mbound mdl κ m η L P t) True
          (fun x => mdl.c * (S - x) + mdl.K + mdl.H S t +
            mdl.γ * expectedNext mdl.f (fun y => J y (t + 1)) S) ∧
        PieceDerivBound mdl.cmax (Mbound mdl κ m η L P t) (HDerivLipschitz mdl t)
          (fun x => mdl.H x t + mdl.γ * expectedNext mdl.f (fun y => J y (t + 1)) x) := by sorry

end ResetInventory
