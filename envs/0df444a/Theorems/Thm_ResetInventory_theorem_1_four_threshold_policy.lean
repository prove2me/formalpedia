-- Prove2me | Theorems.Thm_ResetInventory_theorem_1_four_threshold_policy
-- name    : ResetInventory.theorem_1_four_threshold_policy
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:54.507886+00:00
-- url     : https://prove2.me/theorems/43833188-8fee-4a1e-884a-913f617fbe6f
-- title:
--   Theorem 1 — under (29) a four-threshold $(\sigma,s,S,\Sigma)$ policy is optimal (corrected: Lipschitz clause of the third piece conditional)
-- statement:
--   **Theorem 1 (corrected).** Consider the inventory problem with periodic and controlled resets with horizon $k\ge1$, capacity $c_{\max}\ge0$, ordering costs $c,K\ge0$ and discount factor $0\le\gamma<1$. Let A2 hold for $t=0,\dots,k-1$ (constants $\kappa_t,m_t$), A3 for $t=0,\dots,k$ (constants $\eta_t,L_t$) and A5 (constants $L,P$). Suppose $0\le\gamma\le\min\{\gamma_t\mid t\in\{0,\dots,k-1\}\}$ for
--   $$
--   \gamma_{k-1}=\frac{m_{k-1}}{(Lc_{\max}+P)\,\eta_k},\qquad
--   \gamma_t=\frac{m_t}{(Lc_{\max}+P)(\eta_{t+1}+c+\kappa_{t+1})+m_{t+1}}\quad(t=0,\dots,k-2).\tag{29}
--   $$
--   Then the policy described in Proposition 5 is optimal, and the value function has the structure described in Proposition 6. Precisely, for every solution $J$ of the dynamic programming equations (22):
--
--   1. there is a reset order $\varphi\in[0,c_{\max}]$ attaining $J_0=J(0,0)$;
--   2. for every age $t=0,\dots,k-1$ there are thresholds $0\le\sigma_t\le s_t\le\Sigma_t\le+\infty$ and an order-up-to level $S_t\in[0,c_{\max}]$ (with $s_t\le S_t$ when $\sigma_t<s_t$) such that at every $x\in[0,c_{\max}]$ the action of the four-threshold policy (23) (reset and order $\varphi$ on $[0,\sigma_t)$, order up to $S_t$ on $[\sigma_t,s_t)$, do nothing on $[s_t,\Sigma_t)$, reset and order $\varphi$ on $[\Sigma_t,\infty)$) attains the minimum in (22), and $J(x,t)$ has the four-piece form (28);
--   3. each of the three piece functions of (28) has on $[0,c_{\max}]$ a continuous derivative bounded in absolute value by $M_t=\eta_t+c+\kappa_t+m_t/(Lc_{\max}+P)$, the derivatives of the first two pieces are Lipschitz on $[0,c_{\max}]$, and that of $H(x,t)+\gamma\,\mathbb E\,J((x-w)^+,t+1)$ is Lipschitz on $[0,c_{\max}]$ if $\partial_xH(\cdot,t)$ is.
--
--   This is an $(s,S)$ policy wrapped in two reset thresholds. The value function is neither convex nor $K$-convex, because the reset option takes a minimum with a concave function. The discount bound (29) is what keeps the no-reset cost convex at every age of the backward induction.
--
--   Differences from the source:
--   - correction: each piece of (28) has a Lipschitz derivative → each piece has a derivative on [0, c_max] that is continuous and bounded by M_t; the derivatives of the reset piece and of the order-up-to piece are Lipschitz, and that of the piece H(x,t) + γE J((x−w)⁺,t+1) is Lipschitz if ∂ₓH(·,t) is Lipschitz on [0, c_max]; reason: false as printed: k = 1, c_max = 2, γ = 0, c = 1/2, K = 0, R ≡ 0, f(w) = (1 − |w − 1|)⁺, H(z,0) = (z−1)²/2 + εφ(z) with φ'' = Σ_{n≥2} n β(n⁴(z − 1 − 1/n)) (β a smooth bump) satisfies A1–A5 and (29) with ∂ₓₓH ≥ 1, but ∂ₓₓH(1 + 1/n, 0) ≥ εn is unbounded; a right-neighbourhood of x = 1 lies in the do-nothing region for every choice of thresholds, where J(x,0) = H(x,0) has a non-Lipschitz derivative (the appendix's 'Lipschitz because twice differentiable by A2', p.35, is the gap)
--   - reading: an optimal policy (for problem (2)) → for every solution J of the dynamic programming equations (22), the policy's action is feasible and its value equals J(x,t), i.e. it attains the minimum in (22); reason: the paper proves optimality with respect to (22) (p.14: 'the optimal fixed point policy π* … to (22)'); the link from (22) to (2) is Proposition 1, cited from Mintz et al. (2017) and not proved in the paper
--   - reading: A3 for t = 0, …, k − 1 → A3 for t = 0, …, k; reason: (29) uses η_k, and the proof of Theorem 1 takes 'M_k = η_k using A3' (p.35); η_k is otherwise undefined
--   - reading: states x ∈ ℝ₊ (A1), with AT on the domain [0, c_max] → every state, equation and conclusion on x ∈ [0, c_max]; reason: AT and the proofs of Propositions 5 and 6 work on [0, c_max]; from x ≤ c_max the dynamics stay in [0, c_max], and for x > c_max the order set U = [0, c_max − x] of A4 is empty
--   - generalization: §2 setting: g ≥ 0 and s ≥ 0 continuous, s(ζ,t,w) ≡ 0 → no sign, continuity or s(ζ,·,·) ≡ 0 condition on H and R beyond A2 and A3; reason: the proofs never use these conditions (continuity of H and R follows from A2 and A3); every instance of the paper satisfies the remaining hypotheses
--   - generalization: the derivative of each piece (on its region of (28)) → the derivative claims for each piece formula on all of [0, c_max]; reason: the piece formulas are defined on all of [0, c_max]; the claim on [0, c_max] implies the claim on each region
--   - encoding: 0 ≤ γ ≤ min{γ_t} with γ_t from (29) → 0 ≤ γ, γ·((L c_max + P)·η_k) ≤ m_{k−1}, and γ·((L c_max + P)(η_{t+1} + c + κ_{t+1}) + m_{t+1}) ≤ m_t for t + 2 ≤ k; reason: equal to (29) when the denominators are positive (the second always is, since m_{t+1} > 0); at η_k = 0 the paper's γ_{k−1} is undefined and imposes no bound
--   - encoding: thresholds (s_t, S_t, σ_t, Σ_t) defining the four intervals of (23) → ∃ σ_t ≤ s_t ≤ Σ_t in EReal with 0 ≤ σ_t, S_t ∈ [0, c_max], and s_t ≤ S_t when σ_t < s_t; reason: the paper's thresholds may be +∞ (p.33, Figure 6) and its four intervals must partition [0, ∞) for (23) to define a policy; S_t ≥ s_t makes the order S_t − x positive on [σ_t, s_t), as in the paper's construction s_t = s'_t ≤ S'_t
--   - encoding: stage cost g(ξ,τ,u,w) and reset cost s(x,t,w), with E g = cu + K·1(u>0) + H(ξ+u,τ) (A2) and R = E s (A3) → the model carries c, K, H and R; reason: g and s enter (22) only through these expectations; same instances
--   - encoding: derivatives ∂ₓH, ∂ₓₓH, ∂ₓR, ∂_zJ_i and the derivatives in the conclusions → derivatives within [0, c_max] (one-sided at 0 and c_max), with the derivative functions named explicitly; reason: at interior points this is the ordinary derivative; at the ends the paper's functions live on [0, c_max], and its retail example (∂ₓₓH = (p+q)f with a jump of f at 0) needs one-sided derivatives
--   - encoding: horizon k (with t_n ≤ k and the indices k − 1, k − 2 of (29)) → 1 ≤ k; reason: (29) and the min over t ∈ {0, …, k−1} need k ≥ 1; at k = 0 the conclusion would be empty
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Theorem 1, (29), p.21; proof, p.35; Propositions 5–6, pp.19–21

import Mathlib
import Definitions.Def_ResetInventory_A2
import Definitions.Def_ResetInventory_A3
import Definitions.Def_ResetInventory_A5
import Definitions.Def_ResetInventory_IsDPSolution
import Definitions.Def_ResetInventory_policy
import Definitions.Def_ResetInventory_IsOptimalAction
import Definitions.Def_ResetInventory_form28
import Definitions.Def_ResetInventory_Mbound
import Definitions.Def_ResetInventory_PieceDerivBound
import Definitions.Def_ResetInventory_HDerivLipschitz

namespace ResetInventory

/-- **Theorem 1** of Lee, Mintz, Aswani, Shen, Yang, *Optimal Policy for Inventory Management with
Periodic and Controlled Resets*, arXiv:2209.03571v1, p.21, with the Lipschitz clause of
Proposition 6 corrected. Suppose `0 ≤ γ ≤ min{γ_t | t ∈ {0, …, k − 1}}` for
`γ_{k−1} = m_{k−1} / ((L c_max + P) η_k)` and
`γ_t = m_t / ((L c_max + P)(η_{t+1} + c + κ_{t+1}) + m_{t+1})` for `t = 0, …, k − 2` (29). If A1–A5
hold, then the policy described in Proposition 5 is optimal and the value function has the
structure described in Proposition 6.

Lean: for every solution `J` of the dynamic programming equations (22) there is a reset order
`ϕ ∈ [0, c_max]` attaining `J₀ = J(0, 0)`, and for every age `t < k` there are thresholds
`0 ≤ σ_t ≤ s_t ≤ Σ_t ≤ +∞` and an order-up-to level `S_t ∈ [0, c_max]` (with `s_t ≤ S_t` when
`σ_t < s_t`) such that, at every `x ∈ [0, c_max]`, the action of the four-threshold policy (23)
attains the minimum in (22) and `J(x, t)` has the form (28); and each of the three piece functions
of (28) has on `[0, c_max]` a continuous derivative bounded in absolute value by
`M_t = η_t + c + κ_t + m_t / (L c_max + P)`; the derivatives of the first two are Lipschitz on
`[0, c_max]`, and that of the third is Lipschitz on `[0, c_max]` if `∂ₓH(·, t)` is.

**Formalization Note**
* Correction: Proposition 6 asserts Lipschitz derivatives unconditionally, which fails for the
  third piece when `∂ₓₓH(·, t)` is unbounded (Assumption 2 bounds it only from below); that
  piece's Lipschitz clause is conditional on `HDerivLipschitz mdl t`, the rest is as printed.
* A3 is assumed for `t = 0, …, k` (the paper's (29) uses `η_k`, and its proof takes `M_k = η_k`
  "using A3", p.35); A2 for `t = 0, …, k − 1`.
* (29) is multiplicative: `γ (L c_max + P) η_k ≤ m_{k−1}` and
  `γ ((L c_max + P)(η_{t+1} + c + κ_{t+1}) + m_{t+1}) ≤ m_t` for `t + 2 ≤ k` (equal to the
  paper's bounds when the denominators are positive; at `η_k = 0` the paper's `γ_{k−1}` is
  undefined and means no bound).
* "Optimal" is attainment of the minima in (22) (`IsOptimalAction`; Proposition 1 is cited by the
  paper and not formalized). The state domain is `[0, c_max]`. The costs enter through `c, K, H`
  (A2, (24)) and `R = E s` (A3). Derivatives are within `[0, c_max]` (one-sided at the ends).
  Thresholds are in `EReal`. `k ≥ 1`. -/
theorem theorem_1_four_threshold_policy (mdl : ResetModel) (κ m η Lt : ℕ → ℝ) (L P : ℝ)
    (hk : 1 ≤ mdl.k) (hcmax : 0 ≤ mdl.cmax) (hc : 0 ≤ mdl.c) (hK : 0 ≤ mdl.K)
    (hγ0 : 0 ≤ mdl.γ) (hγ1 : mdl.γ < 1)
    (hA2 : ∀ t < mdl.k, A2 mdl κ m t) (hA3 : ∀ t ≤ mdl.k, A3 mdl η Lt t)
    (hA5 : A5 mdl.f L P)
    (h29_last : mdl.γ * ((L * mdl.cmax + P) * η mdl.k) ≤ m (mdl.k - 1))
    (h29 : ∀ t : ℕ, t + 2 ≤ mdl.k →
      mdl.γ * ((L * mdl.cmax + P) * (η (t + 1) + mdl.c + κ (t + 1)) + m (t + 1)) ≤ m t)
    (J : ℝ → ℕ → ℝ) (hJ : IsDPSolution mdl J) :
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
