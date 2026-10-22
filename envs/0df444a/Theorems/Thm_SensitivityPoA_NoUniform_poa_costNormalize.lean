-- Prove2me | Theorems.Thm_SensitivityPoA_NoUniform_poa_costNormalize
-- name    : SensitivityPoA.NoUniform.poa_costNormalize
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:06.173855+00:00
-- url     : https://prove2.me/theorems/f0f620a6-f22f-4412-b493-f493ff73df2d
-- title:
--   §3.5, p. 22 — cost normalizations Ψ_υ map the game space into itself and leave the price of anarchy unchanged
-- statement:
--   Let $(G, K, S)$ satisfy the standing assumptions, let $\Gamma = (\tau, d)$ be a game of the game space $\mathcal G(G,K,S)$, and let $\upsilon > 0$. Then the cost normalization $\Psi_\upsilon(\Gamma) = (\tau/\upsilon, d)$ is again a game of $\mathcal G(G,K,S)$, and
--   $$\rho\big(\Psi_\upsilon(\Gamma)\big) = \rho(\Gamma).$$
--
--   Dividing all costs by a common positive factor changes neither which flows are Wardrop equilibria nor which are optimal, and scales the WE cost and the SO cost by the same factor $1/\upsilon$. The price of anarchy is therefore invariant under cost normalizations; this invariance, combined with the scaling (3.11) of the distance, drives both parts of Theorem 8.
--
--   **Formalization Note.** The page states the invariance in prose ("ρ(·) is then invariant w.r.t. arbitrary cost normalizations Ψυ(·)"); the membership $\Psi_\upsilon(\Gamma) \in \mathcal G(G,K,S)$ is part of the page's definition of $\Psi_\upsilon$ as an operator on the game space and is stated as a conclusion here.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), pp. 21–22, §3.5 (cost normalization, invariance of ρ)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_NoUniform_Setting

namespace SensitivityPoA.NoUniform

theorem poa_costNormalize (N : Network) (hN : N.Standing) (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (υ : ℝ) (hυ : 0 < υ) :
    costNormalize υ Γ ∈ gameSpace N ∧ PoA (costNormalize υ Γ) = PoA Γ := by sorry

end SensitivityPoA.NoUniform
