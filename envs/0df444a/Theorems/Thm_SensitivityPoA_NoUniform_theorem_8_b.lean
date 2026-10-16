-- Prove2me | Theorems.Thm_SensitivityPoA_NoUniform_theorem_8_b
-- name    : SensitivityPoA.NoUniform.theorem_8_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:30.510605+00:00
-- url     : https://prove2.me/theorems/851bc11f-5f1d-4d3a-ae28-d42a759fc9dc
-- title:
--   Theorem 8b), p. 25 — no game has the whole game space as a Hölder neighborhood of the price of anarchy, for any exponent γ > 0
-- statement:
--   Let $(G, K, S)$ satisfy the standing assumptions and the antichain condition, let $\Gamma$ be a game of the game space $\mathcal G(G,K,S)$, and let $\gamma > 0$. Then $\mathcal G(G,K,S)$ is **not** a $\gamma$-neighborhood of $\Gamma$: there is no constant $\varkappa_\Gamma > 0$ with
--   $$|\rho(\Gamma) - \rho(\Gamma')| \le \varkappa_\Gamma \cdot \|\Gamma - \Gamma'\|^{\gamma} \qquad \text{for all } \Gamma' \in \mathcal G(G,K,S).$$
--   Equivalently, for every $\varkappa > 0$ some game $\Gamma'$ of the game space violates this bound.
--
--   Here $\rho$ is the price of anarchy and $\|\cdot\|$ the distance (3.3). The page states: for every open $U \subseteq \mathcal G(G,K,S)$ and every $\gamma > 0$, if $U$ is a $\gamma$-neighborhood of a game $\Gamma$ then $U \neq \mathcal G(G,K,S)$. So Hölder continuity of $\rho$ at a game, even with a constant depending on the game, can only hold locally.
--
--   **Formalization Note.** A $\gamma$-neighborhood of $\Gamma$ (p. 24) is an open $U \ni \Gamma$ with a constant $\varkappa_\Gamma > 0$ such that the bound holds on $U$. For $U = \mathcal G(G,K,S)$, openness and $\Gamma \in U$ hold automatically, so the theorem is stated directly as the impossibility of the bound on the whole game space. The antichain condition is an added hypothesis (see `Setting`); every game ranges over the game space, so junk values of $\rho$ outside it play no role. The power is the real power `rpow`.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 25, Theorem 8 b); γ-neighborhood, p. 24

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_NoUniform_Setting

namespace SensitivityPoA.NoUniform

theorem theorem_8_b (N : Network) (hN : N.Standing) (hA : N.Antichain)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N) (γ : ℝ) (hγ : 0 < γ) :
    ¬ ∃ κ : ℝ, 0 < κ ∧ ∀ Γ' ∈ gameSpace N, |PoA Γ - PoA Γ'| ≤ κ * gameDist Γ Γ' ^ γ := by sorry

end SensitivityPoA.NoUniform
