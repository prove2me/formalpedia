-- Prove2me | Theorems.Thm_SensitivityPoA_Continuity_lemma_4_ab
-- name    : SensitivityPoA.Continuity.lemma_4_ab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:59.321504+00:00
-- url     : https://prove2.me/theorems/b44452ac-2c11-467b-b814-eadc4098d9ee
-- title:
--   Lemma 4a–b, p. 16 — symmetry, nonnegativity and zero distance
-- statement:
--   For generalized games $\Gamma_1,\Gamma_2,\Gamma_3$ on the fixed network, the distance of (3.3) is symmetric and nonnegative, and it vanishes precisely when the first two games are equivalent:
--   $$\operatorname{Dist}(\Gamma_1,\Gamma_2)=\operatorname{Dist}(\Gamma_2,\Gamma_1)\ge0,\qquad \operatorname{Dist}(\Gamma_1,\Gamma_2)=0\iff\Gamma_1\simeq\Gamma_2.$$
--   These are the first two parts of the metric statement for games modulo equivalence.
--
--   **Formalization Note** Generalized games require nonnegative demands and cost functions that are continuous, monotone, and nonnegative on $[0,\infty)$; they need not satisfy Condition 2. The third game is included because Lemma 4 begins with three arbitrary generalized games.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 16, Lemma 4a)–b)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Continuity_Setting

namespace SensitivityPoA.Continuity

theorem lemma_4_ab (N : Network) (hN : N.Standing)
    (Γ₁ Γ₂ Γ₃ : Game N)
    (h₁ : Γ₁.IsGeneralized) (h₂ : Γ₂.IsGeneralized)
    (h₃ : Γ₃.IsGeneralized) :
    gameDist Γ₁ Γ₂ = gameDist Γ₂ Γ₁ ∧
    0 ≤ gameDist Γ₁ Γ₂ ∧
    (gameDist Γ₁ Γ₂ = 0 ↔ Γ₁.Equiv Γ₂) := by sorry

end SensitivityPoA.Continuity
