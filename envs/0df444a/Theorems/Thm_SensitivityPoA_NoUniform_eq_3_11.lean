-- Prove2me | Theorems.Thm_SensitivityPoA_NoUniform_eq_3_11
-- name    : SensitivityPoA.NoUniform.eq_3_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:59.603748+00:00
-- url     : https://prove2.me/theorems/ffa4aaa7-3cb2-4027-b1ad-a6a09f239016
-- title:
--   (3.11), p. 22 — a cost normalization Ψ_υ divides the distance of two games with equal demands by υ
-- statement:
--   Let $\Gamma = (\tau, d)$ and $\Gamma' = (\sigma, d')$ be games of the game space $\mathcal G(G,K,S)$ with the same demand vector, $d = d'$, and let $\upsilon > 0$. Then
--   $$\|\Psi_\upsilon(\Gamma) - \Psi_\upsilon(\Gamma')\| = \frac{\|\Gamma - \Gamma'\|}{\upsilon},$$
--   where $\|\cdot\|$ is the distance (3.3) and $\Psi_\upsilon(\tau, d) = (\tau/\upsilon, d)$ is the cost normalization.
--
--   With equal demands the demand term of the distance vanishes and the two cost terms are divided by $\upsilon$. Together with the invariance of $\rho$ under $\Psi_\upsilon$, this lets one push two games with different prices of anarchy arbitrarily close together, which is the mechanism behind Theorem 8a).
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 22, eq. (3.11)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_NoUniform_Setting

namespace SensitivityPoA.NoUniform

theorem eq_3_11 (N : Network) (Γ Γ' : Game N) (hΓ : Γ ∈ gameSpace N) (hΓ' : Γ' ∈ gameSpace N)
    (hd : Γ.d = Γ'.d) (υ : ℝ) (hυ : 0 < υ) :
    gameDist (costNormalize υ Γ) (costNormalize υ Γ') = gameDist Γ Γ' / υ := by sorry

end SensitivityPoA.NoUniform
