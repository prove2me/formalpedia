-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_4_11
-- name    : TradingPostNSW.Leontief.Supplement.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:37:00.176621+00:00
-- url     : https://prove2.me/theorems/c0657af6-80b0-4718-86b6-b19b3399a2a9
-- title:
--   Theorem 4.11, p. 16 — Trading Post without fee has pure Nash equilibria for all CES utilities with ρ ∈ (−∞, 1]
-- statement:
--   Let $v_{i,j}\ge0$, budgets $B_i\ge1$, perfect competition (every good valued positively by two distinct agents) and a common parameter $\rho\le1$. Every agent has the CES utility
--   $$u_i(x)=\Big(\sum_{j:\,v_{i,j}>0}v_{i,j}x_j^{\rho}\Big)^{1/\rho}\quad(\rho\ne0),$$
--   which for $\rho<0$ is $0$ when some good with $v_{i,j}>0$ is absent, and for $\rho=0$ is the Cobb–Douglas utility $\prod_jx_j^{v_{i,j}}$. Then the Trading Post game with no minimum bid has a pure Nash equilibrium.
--
--   Existence covers the whole family between perfect substitutes ($\rho=1$) and perfect complements ($\rho\to-\infty$), where Theorem 4.3 shows existence can fail in the Leontief limit.
--
--   Differences from the source:
--   - reading: ρ ∈ (−∞, 1], while the CES formula of p. 7 excludes ρ = 0 → for ρ = 0 the Cobb–Douglas utility Π_j x_j^{v_{i,j}}; reason: the proof (p. 24) treats ρ = 0 as Cobb–Douglas; the exponents v_{i,j} instead of normalized ones are a positive power of the same utility and give the same equilibria
--   - encoding: (Σ_j v_{ij} x_j^ρ)^{1/ρ} → the sum over goods with v_{i,j} > 0, and value 0 for ρ < 0 when such a good is absent; reason: the continuous extension of the formula; Lean's 0^ρ = 0 for ρ < 0 is never used
--   - encoding: the Trading Post allocation x_{i,j} = b_{i,j}/Σ_k b_{k,j} if b_{i,j} > 0, else 0 (p. 12) → the base allocation of TP(0), whose effective bids equal the bids for every b ≥ 0; reason: the same allocation on every strategy profile
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 16, Theorem 4.11; CES p. 7; proof pp. 24–25 (Appendix C)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_4_11 {n m : ℕ} (I : Instance n m) (hI : LinStanding I)
    (hpc : PerfectCompetition I) (ρ : ℝ) (hρ : ρ ≤ 1) :
    ∃ b : Fin n → Fin m → ℝ, IsPNEU I (ces I ρ) 0 b := by sorry

end TradingPostNSW.Leontief.Supplement
