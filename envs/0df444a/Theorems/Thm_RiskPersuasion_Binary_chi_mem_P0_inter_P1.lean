-- Prove2me | Theorems.Thm_RiskPersuasion_Binary_chi_mem_P0_inter_P1
-- name    : RiskPersuasion.Binary.chi_mem_P0_inter_P1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:33.556987+00:00
-- url     : https://prove2.me/theorems/9c423b76-009b-45ab-9e53-43ca3d2090e8
-- title:
--   Sec. 5.1, p. 23 — under Assumption 1, χ(ω₀, ω₁) ∈ P₀ ∩ P₁: the receiver is indifferent at the maximal mixture
-- statement:
--   Assume $P_0$ and $P_1$ are closed (Assumption 1). Let $\omega_0\in L_0$ be a state at which action $0$ is uniquely optimal under full information, and $\omega_1\in K_1$ a state at which action $1$ is optimal under full information. Then the maximal mixture
--   $$\chi(\omega_0,\omega_1)=\gamma(\omega_0,\omega_1)\,e_{\omega_0}+\big(1-\gamma(\omega_0,\omega_1)\big)\,e_{\omega_1}$$
--   satisfies
--   $$\chi(\omega_0,\omega_1)\in P_0\cap P_1 .$$
--   In particular $\chi(\omega_0,\omega_1)$ is a belief, and the receiver is indifferent between actions $0$ and $1$ at it.
--
--   This gives $K_{01}\subseteq P_0\cap P_1$, the inclusion used both in Lemma 7 ($K_{01}\subseteq P_1$) and in showing that solutions of the linear program (10) are feasible for program (7).
-- source:
--   Anunrojwong, Iyer & Lingenbrink, Persuading Risk-Conscious Agents: A Geometric Approach, arXiv:2208.03758v3, p. 23, Section 5.1, text before Eq. (9)

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model

namespace RiskPersuasion.Binary

theorem chi_mem_P0_inter_P1 {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (ρ : (Ω → ℝ) → Fin 2 → ℝ) (hA1 : Assumption1 ρ)
    (ω₀ ω₁ : Ω) (h₀ : ω₀ ∈ L0 ρ) (h₁ : ω₁ ∈ K1 ρ) :
    χ ρ ω₀ ω₁ ∈ P ρ 0 ∩ P ρ 1 := by sorry

end RiskPersuasion.Binary
