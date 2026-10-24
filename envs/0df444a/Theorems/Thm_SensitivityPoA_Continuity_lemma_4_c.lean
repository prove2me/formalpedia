-- Prove2me | Theorems.Thm_SensitivityPoA_Continuity_lemma_4_c
-- name    : SensitivityPoA.Continuity.lemma_4_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:59.420681+00:00
-- url     : https://prove2.me/theorems/9a2af19b-071e-456c-9dcc-f9d82860395c
-- title:
--   Lemma 4c, p. 17 — triangle inequality for the game distance
-- statement:
--   For three generalized games $\Gamma_1,\Gamma_2,\Gamma_3$ on the same network, the distance of (3.3) satisfies
--   $$\operatorname{Dist}(\Gamma_1,\Gamma_2)\le\operatorname{Dist}(\Gamma_1,\Gamma_3)+\operatorname{Dist}(\Gamma_3,\Gamma_2).$$
--   Together with Lemma 4a–b, this yields a metric after identifying games whose demands and relevant cost restrictions agree.
--
--   **Formalization Note** The distance compares costs on the shared demand interval and also at each game's own total demand. The statement ranges over generalized games, as in the paper.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 17, Lemma 4c)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Continuity_Setting

namespace SensitivityPoA.Continuity

theorem lemma_4_c (N : Network) (hN : N.Standing)
    (Γ₁ Γ₂ Γ₃ : Game N)
    (h₁ : Γ₁.IsGeneralized) (h₂ : Γ₂.IsGeneralized)
    (h₃ : Γ₃.IsGeneralized) :
    gameDist Γ₁ Γ₂ ≤ gameDist Γ₁ Γ₃ + gameDist Γ₃ Γ₂ := by sorry

end SensitivityPoA.Continuity
