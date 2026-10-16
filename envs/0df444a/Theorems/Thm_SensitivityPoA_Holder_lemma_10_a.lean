-- Prove2me | Theorems.Thm_SensitivityPoA_Holder_lemma_10_a
-- name    : SensitivityPoA.Holder.lemma_10_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:26.858898+00:00
-- url     : https://prove2.me/theorems/1694ec61-1217-4b41-a8d5-888a33ddab6f
-- title:
--   Lemma 10a), p. 27 — on a demand slice the SO cost is Lipschitz with constant |A|·T(w)
-- statement:
--   Let $w$ be a demand vector with $T(w) > 0$, and let $\Gamma_1 = (\pi^{(1)}, w)$ and $\Gamma_2 = (\pi^{(2)}, w)$ be two games of the game space with the same demand vector (the demand slice $\mathcal G(G,\mathcal K,\mathcal S)|_w$). Then
--   $$|\mathcal C^*(\Gamma_1) - \mathcal C^*(\Gamma_2)| \le |A|\cdot T(w)\cdot\|\Gamma_1 - \Gamma_2\|.$$
--
--   On a demand slice the optimal cost therefore moves at most linearly in the distance of the cost functions.
--
--   **Formalization Note** $\|\Gamma_1 - \Gamma_2\|$ is the distance (3.3); on a demand slice it is the largest difference of the cost functions on $[0, T(w)]$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 27, Lemma 10a)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

namespace SensitivityPoA.Holder
open KellyStochasticNetworks

/-- Lemma 10a), p. 27: on a demand slice the SO cost is Lipschitz with constant `|A|·T(w)`. -/
theorem lemma_10_a (N : Network) (hN : N.Standing) (Γ1 Γ2 : Game N)
    (h1 : Γ1 ∈ gameSpace N) (h2 : Γ2 ∈ gameSpace N) (hd : Γ1.d = Γ2.d) :
    |SOCost Γ1 - SOCost Γ2| ≤ (N.J : ℝ) * totalDemand Γ1.d * gameDist Γ1 Γ2 := by sorry

end SensitivityPoA.Holder
