-- Prove2me | Theorems.Thm_RiskPersuasion_Binary_lemma_6
-- name    : RiskPersuasion.Binary.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:34.373064+00:00
-- url     : https://prove2.me/theorems/d5644277-563f-472f-9146-c27390eb9d93
-- title:
--   Lemma 6 — Δ(Ω) = Conv(L₀ ∪ K₀₁) ∪ Conv(K₁ ∪ K₀₁)
-- statement:
--   For every receiver utility $\rho$ in the binary model, the simplex of beliefs splits into two convex hulls of finite point sets:
--   $$\Delta(\Omega)=\operatorname{Conv}(L_0\cup K_{01})\ \cup\ \operatorname{Conv}(K_1\cup K_{01}),$$
--   where the states in $L_0$ and $K_1$ stand for their point masses $e_\omega$, and $K_{01}$ is the set of maximal mixtures $\chi(\omega_0,\omega_1)$, $\omega_0\in L_0$, $\omega_1\in K_1$.
--
--   No assumption on $\rho$ is needed. The lemma is the geometric decomposition behind Lemma 7 and Theorem 3: every belief, and in particular every mean-posterior of action $0$, is a convex combination either of $L_0$ and $K_{01}$ or of $K_1$ and $K_{01}$.
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 40, Lemma 6

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model

namespace RiskPersuasion.Binary

theorem lemma_6 {Ω : Type} [Fintype Ω] [DecidableEq Ω] (ρ : (Ω → ℝ) → Fin 2 → ℝ) :
    stdSimplex ℝ Ω =
      convexHull ℝ (e '' L0 ρ ∪ K01 ρ) ∪ convexHull ℝ (e '' K1 ρ ∪ K01 ρ) := by sorry

end RiskPersuasion.Binary
