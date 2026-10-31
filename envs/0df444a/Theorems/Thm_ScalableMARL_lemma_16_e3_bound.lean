-- Prove2me | Theorems.Thm_ScalableMARL_lemma_16_e3_bound
-- name    : ScalableMARL.lemma_16_e3_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:46.868475+00:00
-- url     : https://prove2.me/theorems/d3ea0506-a24d-4b36-bc12-bf2724731d3c
-- title:
--   Lemma 16 — if $T+1\ge(\log\frac{c(1-\gamma)}{\bar r}+(\kappa+1)\log\rho)/\log\gamma$, then $\|h(\theta)-\nabla J(\theta)\|\le2\frac{Lc}{1-\gamma}\rho^{\kappa+1}$
-- statement:
--   Assume Assumption 1 ($0\le r_i\le\bar r$), Assumption 2 ($(c,\rho)$-exponential decay at $\kappa$ with $\rho\le\gamma$, and $c,\rho>0$) and the gradient bound of Assumption 4 ($\|\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)\|\le L_i$, $L=\sqrt{\sum_iL_i^2}$), with policies that are distributions, positive and differentiable in their parameters. If
--   $$T+1\ge\frac{\log\frac{c(1-\gamma)}{\bar r}+(\kappa+1)\log\rho}{\log\gamma},$$
--   then for every policy $\theta$
--   $$\|e^3\|=\|h(\theta)-\nabla J(\theta)\|\le2\,\frac{Lc}{1-\gamma}\,\rho^{\kappa+1},$$
--   where $h(\theta)$ is the truncated, finite-horizon policy gradient (27); in particular $\|e^3(m)\|=\|h(m)-\nabla J(\theta(m))\|$ obeys this bound along every run of SAC.
--
--   The error $e^3$ has two sources, the truncation of the Q-functions to κ-hop neighbourhoods and the truncation of the discounted sum at $T$; the condition on $T$ makes the second as small as the first.
--
--   **Formalization Note** $h(\theta)$ depends only on the policy, so the statement is deterministic and quantifies over all $\theta$.
--
--   Differences from the source:
--   - generalization: e³(m) at the iterate θ(m), almost surely → h(θ) − ∇J(θ) for every policy θ; reason: h(m) = h(θ(m)) depends only on θ(m), so the page's claim is the case θ = θ(m)
--   - generalization: the standing hypotheses of Theorem 4 → only Assumptions 1, 2 and the gradient bound of Assumption 4; reason: the statement holds without the others, which are part of Theorem 4's
--   - encoding: c, ρ unqualified → c > 0 and ρ > 0; reason: presupposed by log(c(1−γ)/r̄) and log ρ; excludes only cases where the condition on T is undefined
--   - reading: Definition 1 with κ unspecified, in Assumption 2 → the exponential decay property at the algorithm's κ; reason: κ is the algorithm's fixed parameter throughout; the proof uses only that κ
--   - encoding: expectations over the networked MDP → finite sums over the finite state and action spaces (Q_j^θ through the published one-step form r_j + γPV, π_t^θ through the time-t state law); reason: all spaces are finite, so these are the same numbers
--   - encoding: agents N = {1, …, n}, finite local sets S_i, A_i → Fin n and finite types; reason: Lean indexing
--   - reading: localized policies parameterized by θ_i (parameter space unnamed, norms Euclidean) → θ_i ∈ ℝ^{d_i}, θ in PiLp 2 with the Euclidean norm of the whole tuple; reason: the page differentiates in θ and uses Euclidean norms
--   - encoding: ∇_{θ_i} log ζ_i^{θ_i}(a_i|s_i) used as given → ζ_i^{θ_i}(a_i|s_i) > 0 and θ_i ↦ ζ_i^{θ_i}(a_i|s_i) differentiable; reason: presupposed for the gradient of the logarithm to exist; excludes only cases where the printed quantities are undefined
--   - encoding: the bounds S, A of Assumption 1 → real numbers Sb, Ab; reason: the page does not restrict them to integers; they do not enter this statement
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 21, Lemma 16 (with eqs. (27)–(28))

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP
import Definitions.Def_ScalableMARL_Assumptions
import Definitions.Def_ScalableMARL_SAC

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Lemma 16 (the truncation term `e³`).** Qu, Wierman & Li, arXiv:1912.02906v3, p. 21, Lemma 16:
when `T + 1 ≥ (log(c(1 − γ)/r̄) + (κ + 1) log ρ)/log γ`, almost surely
`‖e³(m)‖ ≤ 2 (Lc/(1 − γ)) ρ^{κ+1}`, where `e³(m) = h(m) − ∇J(θ(m))` (28).

**Formalization Note.** `h(m) = h(θ(m))` depends only on `θ(m)`, so the statement is given for
every policy `θ`: `‖h(θ) − ∇J(θ)‖ ≤ 2(Lc/(1 − γ))ρ^{κ+1}`. Assumptions 1, 2 (with `c, ρ > 0`, which
the logarithms presuppose) and the bound `‖∇_{θ_i} log ζ_i‖ ≤ L_i` of Assumption 4 are assumed. -/
theorem lemma_16_e3_bound (M : NetMDP n S A) (pol : LocalPolicyClass n S A)
    (hM : M.Valid) (hpol : pol.IsDistribution) (hpd : pol.PositiveDifferentiable)
    (rbar Sb Ab c ρ : ℝ) (L : Fin n → ℝ) (κ T : ℕ)
    (hA1 : Assumption1 M rbar Sb Ab) (hc : 0 < c) (hρ : 0 < ρ)
    (hA2 : Assumption2 M pol c ρ κ) (hA4 : LogGradBound pol L)
    (hT : (Real.log (c * (1 - M.γ) / rbar) + (κ + 1) * Real.log ρ) / Real.log M.γ ≤ T + 1)
    (θ : pol.Param) :
    ‖hvec M pol κ T θ - gradient (J M pol) θ‖ ≤ 2 * (Lnorm L * c / (1 - M.γ)) * ρ ^ (κ + 1) := by sorry

end ScalableMARL
