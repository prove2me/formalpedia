-- Prove2me | Theorems.Thm_PowerTwoChoices_Limit_theorem_3
-- name    : PowerTwoChoices.Limit.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:18.123595+00:00
-- url     : https://prove2.me/theorems/39c99d4e-38a0-45ff-93c6-b7a0d54afab2
-- title:
--   Theorem 3 — a weighted $L_1$ potential $\Phi(t)=\sum_i w_i|s_i(t)-\pi_i|$ converges exponentially to $0$
-- statement:
--   Let $d\ge2$ and $0<\lambda<1$, and let $\pi_i=\lambda^{(d^i-1)/(d-1)}$ be the fixed point of the limiting supermarket system (1). There exist constants $w_i\ge1$ ($i\ge1$), depending only on $\lambda$ and $d$, such that for every trajectory $s(t)$ of (1) the potential
--   $$\Phi(t)=\sum_{i=1}^\infty w_i\,|s_i(t)-\pi_i|$$
--   has the following properties.
--
--   1. If $\Phi(0)<\infty$, then $\Phi$ converges exponentially to $0$: there are $\delta>0$ and $c_0$ with $\Phi(t)\le c_0e^{-\delta t}$ for all $t\ge0$.
--   2. In particular, if $s_j(0)=0$ for some $j$, then $\Phi$ converges exponentially to $0$.
--
--   This is the paper's convergence theorem: from any reasonable starting point, the limiting system approaches its fixed point exponentially fast in a weighted $L_1$ sense.
--
--   **Formalization Note.** The weights are chosen before the trajectory. $\Phi$ is computed in $[0,\infty]$, so "$\Phi(0)<\infty$" is literal. The constants $\delta$ and $c_0$ may depend on the trajectory (Definition 2). The paper writes its proof for $d=2$; the statement is for every $d\ge2$.
-- source:
--   Mitzenmacher, The Power of Two Choices in Randomized Load Balancing, IEEE Trans. Parallel Distrib. Syst. 12(10), 2001, p. 1098, Theorem 3 (with Definition 2, p. 1097)

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

open scoped ENNReal
open Filter Topology

namespace PowerTwoChoices.Limit

/-- Theorem 3 (Mitzenmacher 2001, p. 1098). Let `d ≥ 2` and `0 < λ < 1`. There are constants
`w_i ≥ 1` (`i ≥ 1`), fixed before any trajectory is chosen, such that for every trajectory the
potential `Φ(t) = ∑_{i ≥ 1} w_i |s_i(t) - π_i|` converges exponentially to `0`
(Definition 2) whenever `Φ(0) < ∞`, and in particular whenever `s_j(0) = 0` for some `j`. -/
theorem theorem_3 (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ w : ℕ → ℝ, (∀ i : ℕ, 1 ≤ i → 1 ≤ w i) ∧
      ∀ s : ℝ → ℕ → ℝ, IsTrajectory lam d s →
        (potential lam d w (s 0) < ⊤ →
          ConvergesExponentially (fun t => potential lam d w (s t))) ∧
        ((∃ j : ℕ, s 0 j = 0) →
          ConvergesExponentially (fun t => potential lam d w (s t))) := by sorry

end PowerTwoChoices.Limit
