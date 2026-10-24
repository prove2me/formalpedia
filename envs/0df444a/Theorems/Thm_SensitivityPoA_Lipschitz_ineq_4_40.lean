-- Prove2me | Theorems.Thm_SensitivityPoA_Lipschitz_ineq_4_40
-- name    : SensitivityPoA.Lipschitz.ineq_4_40
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:41.729391+00:00
-- url     : https://prove2.me/theorems/918a307a-de71-4059-911b-100835efc215
-- title:
--   (4.40), p. 38, first four inequalities — strong monotonicity m·Σ|g̃ₐ − f̃ₐ|² ≤ … ≤ ‖Γ₁ − Γ₂‖·Σ|g̃ₐ − f̃ₐ|
-- statement:
--   Let $\Gamma_1=(\pi^{1},w)$ and $\Gamma_2=(\pi^{2},w)$ be two games in the game space $\mathcal G(G,K,S)$ with the same demand vector $w$, total demand $T=T(w)$. Assume that every cost $\pi^1_a$ of $\Gamma_1$ is continuously differentiable on $[0,T]$ with $(\pi^1_a)'(x)\ge m$ for all $x\in[0,T]$, for a constant $m>0$. Let $\tilde f$ be a Wardrop equilibrium of $\Gamma_1$ and $\tilde g$ one of $\Gamma_2$, with arc flows $\tilde f_a$, $\tilde g_a$. Then
--   $$\begin{aligned}0&\le m\sum_{a\in A}|\tilde g_a-\tilde f_a|^2\le\sum_{a\in A}\big(\pi^1_a(\tilde g_a)-\pi^1_a(\tilde f_a)\big)(\tilde g_a-\tilde f_a)\\&\le\sum_{a\in A}\big(\pi^1_a(\tilde g_a)-\pi^2_a(\tilde g_a)\big)(\tilde g_a-\tilde f_a)\le\|\Gamma_1-\Gamma_2\|\cdot\sum_{a\in A}|\tilde g_a-\tilde f_a|.\end{aligned}$$
--
--   The chain says that the arc flows of the two equilibria differ by at most a multiple of $\|\Gamma_1-\Gamma_2\|$; it is the core estimate behind the local Lipschitz continuity of the price of anarchy at games with strictly increasing $C^1$ costs (Theorem 12b)).
--
--   **Formalization Note** The paper states (4.40) for the auxiliary game $\Gamma''=(\hat\tau,d')$ of (4.34)–(4.35) and the game $\Gamma'=(\sigma,d')$; here the first four inequalities are posed for two arbitrary games of one demand slice ($\hat\tau\mapsto\pi^1$, $\sigma\mapsto\pi^2$, $\|\Gamma'-\Gamma''\|\mapsto\|\Gamma_1-\Gamma_2\|$). The display's fifth step depends on the specific $\Gamma''$ and (4.36) and is not posed. Its last step, $\sum_a|\tilde g_a-\tilde f_a|\le\sqrt{\sum_a|\tilde g_a-\tilde f_a|^2}$, is false in general (the correct bound carries a factor $\sqrt{|A|}$) and is not posed. The derivative is `derivWithin` on $[0,T]$, one-sided at the endpoints.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 38, display (4.40), first four inequalities

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Lipschitz_Setting
import Definitions.Def_SensitivityPoA_Lipschitz_SpecialCosts

namespace SensitivityPoA.Lipschitz
open KellyStochasticNetworks

theorem ineq_4_40 (N : Network) (hN : N.Standing) (Γ₁ Γ₂ : Game N)
    (hΓ₁ : Γ₁ ∈ gameSpace N) (hΓ₂ : Γ₂ ∈ gameSpace N) (hd : Γ₁.d = Γ₂.d)
    (m : ℝ) (hm : 0 < m) (hC1 : C1SlopeOnDemand Γ₁ m)
    (f g : Fin N.R → ℝ) (hf : IsWE Γ₁ f) (hg : IsWE Γ₂ g) :
    0 ≤ m * ∑ j, (linkFlow N.A g j - linkFlow N.A f j) ^ 2 ∧
    m * ∑ j, (linkFlow N.A g j - linkFlow N.A f j) ^ 2 ≤
      ∑ j, (Γ₁.τ j (linkFlow N.A g j) - Γ₁.τ j (linkFlow N.A f j)) *
        (linkFlow N.A g j - linkFlow N.A f j) ∧
    ∑ j, (Γ₁.τ j (linkFlow N.A g j) - Γ₁.τ j (linkFlow N.A f j)) *
        (linkFlow N.A g j - linkFlow N.A f j) ≤
      ∑ j, (Γ₁.τ j (linkFlow N.A g j) - Γ₂.τ j (linkFlow N.A g j)) *
        (linkFlow N.A g j - linkFlow N.A f j) ∧
    ∑ j, (Γ₁.τ j (linkFlow N.A g j) - Γ₂.τ j (linkFlow N.A g j)) *
        (linkFlow N.A g j - linkFlow N.A f j) ≤
      gameDist Γ₁ Γ₂ * ∑ j, |linkFlow N.A g j - linkFlow N.A f j| := by sorry

end SensitivityPoA.Lipschitz
