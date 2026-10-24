-- Prove2me | Theorems.Thm_SensitivityPoA_Lipschitz_ineq_4_39
-- name    : SensitivityPoA.Lipschitz.ineq_4_39
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:56.113991+00:00
-- url     : https://prove2.me/theorems/8b8e9996-14cc-4aff-9fba-c12c3771d9cd
-- title:
--   (4.39), p. 38 — for WE flows of two games with equal demands, the monotone-gap chain bounded by 2·|A|·T·‖Γ₁ − Γ₂‖
-- statement:
--   Let $\Gamma_1=(\pi^{1},w)$ and $\Gamma_2=(\pi^{2},w)$ be two games in the game space $\mathcal G(G,K,S)$ with the same demand vector $w$ and total demand $T=T(w)$. Let $\tilde f$ be a Wardrop equilibrium of $\Gamma_1$ and $\tilde g$ a Wardrop equilibrium of $\Gamma_2$, with arc flows $\tilde f_a$, $\tilde g_a$. Then
--   $$0\le\sum_{a\in A}\big(\pi^{1}_a(\tilde f_a)-\pi^{2}_a(\tilde g_a)\big)(\tilde g_a-\tilde f_a)\le\sum_{a\in A}\big(\pi^{1}_a(\tilde g_a)-\pi^{2}_a(\tilde f_a)\big)(\tilde g_a-\tilde f_a)\le 2\cdot|A|\cdot T\cdot\|\Gamma_1-\Gamma_2\|.$$
--
--   This compares the equilibria of two nearby games of one demand slice. It feeds the strong-monotonicity estimate (4.40) in the proof of Theorem 12b).
--
--   **Formalization Note** The paper states (4.39) for the auxiliary game $\Gamma''=(\hat\tau,d')$ (WE $\tilde f$) and the game $\Gamma'=(\sigma,d')$ (WE $\tilde g$); here it is posed for two arbitrary games of one demand slice, with $\hat\tau\mapsto\pi^1$, $\sigma\mapsto\pi^2$ and $\|\Gamma'-\Gamma''\|\mapsto\|\Gamma_1-\Gamma_2\|$ (the distance is symmetric). Its proof uses only the WE property of $\tilde f,\tilde g$, monotonicity of the costs, and $|\pi^1_a(x)-\pi^2_a(x)|\le\|\Gamma_1-\Gamma_2\|$ on $[0,T]$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 38, display (4.39)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Lipschitz_Setting
import Definitions.Def_SensitivityPoA_Lipschitz_SpecialCosts

namespace SensitivityPoA.Lipschitz
open KellyStochasticNetworks

theorem ineq_4_39 (N : Network) (hN : N.Standing) (Γ₁ Γ₂ : Game N)
    (hΓ₁ : Γ₁ ∈ gameSpace N) (hΓ₂ : Γ₂ ∈ gameSpace N) (hd : Γ₁.d = Γ₂.d)
    (f g : Fin N.R → ℝ) (hf : IsWE Γ₁ f) (hg : IsWE Γ₂ g) :
    0 ≤ ∑ j, (Γ₁.τ j (linkFlow N.A f j) - Γ₂.τ j (linkFlow N.A g j)) *
        (linkFlow N.A g j - linkFlow N.A f j) ∧
    ∑ j, (Γ₁.τ j (linkFlow N.A f j) - Γ₂.τ j (linkFlow N.A g j)) *
        (linkFlow N.A g j - linkFlow N.A f j) ≤
      ∑ j, (Γ₁.τ j (linkFlow N.A g j) - Γ₂.τ j (linkFlow N.A f j)) *
        (linkFlow N.A g j - linkFlow N.A f j) ∧
    ∑ j, (Γ₁.τ j (linkFlow N.A g j) - Γ₂.τ j (linkFlow N.A f j)) *
        (linkFlow N.A g j - linkFlow N.A f j) ≤
      2 * (N.J : ℝ) * totalDemand Γ₁.d * gameDist Γ₁ Γ₂ := by sorry

end SensitivityPoA.Lipschitz
