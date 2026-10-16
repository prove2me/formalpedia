-- Prove2me | Theorems.Thm_SensitivityPoA_NoUniform_theorem_8_a
-- name    : SensitivityPoA.NoUniform.theorem_8_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:10.426206+00:00
-- url     : https://prove2.me/theorems/ba51b10a-932c-4c4a-8807-bbde65090f6c
-- title:
--   Theorem 8a), p. 25 — the price of anarchy is not uniformly Hölder continuous on the game space, for any exponent and constant
-- statement:
--   Let $(G, K, S)$ satisfy the standing assumptions and the antichain condition. Then there are **no** constants $\gamma > 0$ and $\varkappa > 0$ such that
--   $$|\rho(\Gamma) - \rho(\Gamma')| \le \varkappa \cdot \|\Gamma - \Gamma'\|^{\gamma} \qquad \text{for all } \Gamma, \Gamma' \in \mathcal G(G,K,S),$$
--   i.e. the price of anarchy map $\rho$ is not uniformly Hölder continuous on the game space (Definition 3.1 iii)). Here $\|\cdot\|$ is the distance (3.3).
--
--   In particular $\rho$ is not Lipschitz continuous on the whole game space; Hölder continuity of $\rho$ can only hold with a constant depending on the game, which is the form of the paper's positive results.
--
--   **Formalization Note.** The antichain condition is an added hypothesis (see the `Setting` file): it holds for loop-free paths, and without it the statement fails for $S_k = \{\{a\},\{a,b\}\}$. Both games range over the game space only, so the junk value $\rho = 0/0 = 0$ of a degenerate pair $(\tau, d)$ plays no role. The power $\|\Gamma-\Gamma'\|^\gamma$ is the real power `rpow`, which is $0$ at $0$ for $\gamma > 0$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 25, Theorem 8 a); Definition 3.1 iii), p. 21

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_NoUniform_Setting

namespace SensitivityPoA.NoUniform

theorem theorem_8_a (N : Network) (hN : N.Standing) (hA : N.Antichain) :
    ¬ ∃ γ : ℝ, 0 < γ ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ Γ ∈ gameSpace N, ∀ Γ' ∈ gameSpace N,
        |PoA Γ - PoA Γ'| ≤ κ * gameDist Γ Γ' ^ γ := by sorry

end SensitivityPoA.NoUniform
