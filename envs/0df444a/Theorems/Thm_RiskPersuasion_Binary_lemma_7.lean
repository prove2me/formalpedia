-- Prove2me | Theorems.Thm_RiskPersuasion_Binary_lemma_7
-- name    : RiskPersuasion.Binary.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:32.988758+00:00
-- url     : https://prove2.me/theorems/699e05dd-8425-4e64-896b-5a3d90b52ede
-- title:
--   Lemma 7 — under Assumption 2, Conv(P₁) = Conv(K₁ ∪ K₀₁)
-- statement:
--   Assume $P_0$ and $P_1$ are closed (Assumption 1, standing throughout the paper) and that the non-adoption region $P_1^c=\{\mu\in\Delta(\Omega):\hat\rho(\mu)<0\}$ is convex (Assumption 2). Then
--   $$\operatorname{Conv}(P_1)=\operatorname{Conv}(K_1\cup K_{01}),$$
--   where the states in $K_1$ stand for their point masses.
--
--   So the convex hull of the region where action $1$ is optimal is a polytope whose extreme points lie in the finite set $K_1\cup K_{01}$. It turns the constraint $t_1\in\operatorname{Conv}(P_1\cup\{0\})$ of program (7) into the linear constraint $t_1\in\operatorname{Conv}(K_1\cup K_{01}\cup\{0\})$ of program (10), and gives the full-persuasion criterion $\mu^*\in\operatorname{Conv}(K_1\cup K_{01})$ of Section 5.2.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 41, Lemma 7

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model

namespace RiskPersuasion.Binary

theorem lemma_7 {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (ρ : (Ω → ℝ) → Fin 2 → ℝ) (hA1 : Assumption1 ρ) (hA2 : Assumption2 ρ) :
    convexHull ℝ (P ρ 1) = convexHull ℝ (e '' K1 ρ ∪ K01 ρ) := by sorry

end RiskPersuasion.Binary
