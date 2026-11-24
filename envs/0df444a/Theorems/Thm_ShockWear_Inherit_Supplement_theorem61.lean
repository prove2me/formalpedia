-- Prove2me | Theorems.Thm_ShockWear_Inherit_Supplement_theorem61
-- name    : ShockWear.Inherit.Supplement.theorem61
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:01:44.266263+00:00
-- url     : https://prove2.me/theorems/79a094b9-8433-4e92-9fa2-281cb3dc004c
-- title:
--   Theorem 6.1 — independent shock magnitudes with constant, decreasing or increasing F_i(x)
-- statement:
--   Shocks arrive at rate $\lambda>0$; the $i$th shock has magnitude $X_i$ with distribution $F_i$, the magnitudes are independent, and a shock of magnitude exceeding the threshold $x$ destroys the device. Writing $a_i=F_i(x)\in[0,1]$, the probability of surviving $k$ shocks is (6.1)
--   $$\bar P_k=\prod_{i=1}^k a_i,$$
--   and the survival function is (6.2)
--   $$\bar H(t)=\sum_{k=0}^\infty e^{-\lambda t}\frac{(\lambda t)^k}{k!}\prod_{i=1}^k a_i,\qquad t\ge0.$$
--   Then:
--   1. if $a_i=a_1$ for $i=2,3,\dots$, then $\bar H$ is exponential: $\bar H(t)=e^{-ct}$ for $t\ge0$ and some $c\ge0$;
--   2. if $a_i$ is decreasing in $i=1,2,\dots$, then $\bar H$ is IHR;
--   3. if $a_i$ is increasing in $i=1,2,\dots$, then $\bar H$ is DHR.
--
--   The theorem covers, for example, thresholds that are lowered (raised) by each successive shock.
--
--   **Formalization Note** Only the numbers $a_i=F_i(x)$, $i\ge1$, enter the statement, so they are taken as a sequence in $[0,1]$. "Exponential" includes the degenerate rate $c=0$ ($a_i\equiv1$ gives $\bar H\equiv1$). IHR is stated cross-multiplied on all of $\mathbb R$ ($\bar H=1$ on $t<0$; $\bar P_0=1$), DHR cross-multiplied on $t\ge0$, as in the mission's definitions. Monotonicity is weak.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 647, Theorem 6.1, displays (6.1), (6.2); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit.Supplement

/-- Theorem 6.1: with `P̄_k = ∏_{i=1}^k F_i(x)` as in (6.1), equal factors give an
exponential survival function, decreasing factors an IHR one, and increasing
factors a DHR one. Only the numbers `a i = F_i(x) ∈ [0, 1]`, `i ≥ 1`, enter. -/
theorem theorem61 (lam : ℝ) (hlam : 0 < lam) (a : ℕ → ℝ)
    (ha : ∀ i, 1 ≤ i → 0 ≤ a i ∧ a i ≤ 1) :
    ((∀ i, 2 ≤ i → a i = a 1) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ t, 0 ≤ t →
        ShockWear.CumDamage.shockSurv lam (fun k => ∏ i ∈ Finset.Icc 1 k, a i) t = Real.exp (-(c * t))) ∧
    ((∀ i j, 1 ≤ i → i ≤ j → a j ≤ a i) →
      IsIHR (ShockWear.CumDamage.shockSurv lam (fun k => ∏ i ∈ Finset.Icc 1 k, a i))) ∧
    ((∀ i j, 1 ≤ i → i ≤ j → a i ≤ a j) →
      IsDHR (ShockWear.CumDamage.shockSurv lam (fun k => ∏ i ∈ Finset.Icc 1 k, a i))) := by sorry

end ShockWear.Inherit.Supplement
