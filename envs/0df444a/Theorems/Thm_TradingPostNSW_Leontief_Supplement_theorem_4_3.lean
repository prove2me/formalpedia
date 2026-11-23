-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_4_3
-- name    : TradingPostNSW.Leontief.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:35:15.355184+00:00
-- url     : https://prove2.me/theorems/aa311a7d-6cdc-4fa1-8654-60d50d4044d1
-- title:
--   Theorem 4.3, p. 14 — Leontief Trading Post: a pure equilibrium exists iff a market equilibrium has all prices positive; then utilities are unique and the price of anarchy is 1
-- statement:
--   Consider a Leontief instance ($v_{i,j}\ge0$, $B_i\ge1$, every agent demands some good) with perfect competition, and the Trading Post game without entrance fee. Then:
--
--   1. The game has a pure Nash equilibrium **if and only if** the Fisher market of the true valuations has a market equilibrium $(p,x)$ with $p_j>0$ for every good $j$.
--   2. When this happens, all pure Nash equilibria give every agent the same utility: $u_i(x_i(b))=u_i(x_i(b'))$ for all pure equilibria $b,b'$ and every agent $i$.
--   3. The price of anarchy is $1$: every pure Nash equilibrium $b$ induces a feasible allocation $x(b)$ with
--   $$NSW(y)\ \le\ NSW\big(x(b)\big)\quad\text{for every feasible }y.$$
--
--   The theorem identifies when Trading Post implements the market outcome exactly for perfect complements; Example 4.4 shows the condition can fail, which motivates the entrance fee.
--
--   Differences from the source:
--   - reading: the corresponding market equilibrium prices are all strictly positive → some market equilibrium of the true market has all prices positive; reason: equilibrium prices need not be unique; both directions of the proof (Appendix B) use or build one such equilibrium
--   - reading: market equilibrium (p. 7) → the base ε-market equilibrium with ε = 0, with affordable bundles y ≥ 0; reason: with ε = 0 the base definition is exactly conditions (1)–(2) of p. 7 under the base mission's reading y ≥ 0
--   - reading: the price of anarchy is 1 → every pure Nash equilibrium allocation is feasible and maximizes NSW over feasible allocations; reason: an allocation reaching the optimum is what a price of anarchy of 1 asserts
--   - encoding: the Trading Post allocation x_{i,j} = b_{i,j}/Σ_k b_{k,j} if b_{i,j} > 0, else 0 (p. 12) → the base allocation of TP(0), whose effective bids equal the bids for every b ≥ 0; reason: the same allocation on every strategy profile
--   - encoding: Leontief utilities need demanded goods → the base standing assumption, every agent demands a good; reason: the published base convention
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 14, Theorem 4.3; proof pp. 20–21 (Appendix B)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_4_3 {n m : ℕ} (I : Instance n m) (hI : Standing I)
    (hpc : PerfectCompetition I) :
    ((∃ b : Fin n → Fin m → ℝ, IsPNE I 0 b) ↔
        ∃ (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ), IsEpsME I 0 p x ∧ ∀ j, 0 < p j) ∧
      ((∃ (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ), IsEpsME I 0 p x ∧ ∀ j, 0 < p j) →
        ∀ b b' : Fin n → Fin m → ℝ, IsPNE I 0 b → IsPNE I 0 b' →
          ∀ i, u I i (tpAlloc 0 b i) = u I i (tpAlloc 0 b' i)) ∧
      (∀ b : Fin n → Fin m → ℝ, IsPNE I 0 b →
        Feasible I (tpAlloc 0 b) ∧
          ∀ y : Fin n → Fin m → ℝ, Feasible I y → NSW I y ≤ NSW I (tpAlloc 0 b)) := by sorry

end TradingPostNSW.Leontief.Supplement
