-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_5_1
-- name    : TradingPostNSW.Leontief.Supplement.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:43:08.075373+00:00
-- url     : https://prove2.me/theorems/245d6c52-9a78-498d-b634-f71003f7776f
-- title:
--   Theorem 5.1, p. 17 — Nash equilibria of the Fisher mechanism and of Trading Post are proportional; TP(∆) is approximately proportional
-- statement:
--   Let agents have utilities $U_i:[0,1]^m\to\mathbb R$ that are concave, non-decreasing and non-negative, and budgets $B_i\ge1$ with $B=\sum_iB_i$; write $\mathbf 1$ for the bundle containing all of every good.
--
--   1. **Fisher market mechanism.** Agents report concave, non-decreasing, non-negative utilities, and an outcome rule returns a market equilibrium of the reported market (bundles in $[0,1]^m$). At every pure Nash equilibrium $W$, every agent receives $U_i(x_i)\ge\frac{B_i}{B}U_i(\mathbf 1)$.
--   2. **Trading Post.** If moreover every $U_i$ is strictly increasing, every pure Nash equilibrium $b$ of Trading Post without fee gives $U_i(x_i(b))\ge\frac{B_i}{B}U_i(\mathbf 1)$.
--   3. **Trading Post with fee.** For every $0<\Delta<1/m$, every pure Nash equilibrium $b$ of $TP(\Delta)$ with strictly increasing utilities gives
--   $$U_i\big(x_i(b)\big)\ \ge\ \frac{B_i}{B}\,(1-\rho_i)\,U_i(\mathbf 1),\qquad \rho_i=\frac{\Delta\,(m-1)}{B_i}.$$
--
--   Proportionality says that each agent gets at least its budget share of the value of everything, whatever the others do in equilibrium.
--
--   Differences from the source:
--   - generalization: the Fisher market mechanism of Definition 3.1 (removal of unreported goods, selection clause) → every outcome rule returning a market equilibrium of the reported market; reason: the guarantee does not use either clause; the paper's rules are among these, so the statement specializes to the paper's
--   - reading: reports for concave utilities → reports range over concave, non-decreasing, non-negative utility functions, and the optimal-bundle condition ranges over the box [0,1]^m; reason: the proof (p. 30) lets an agent report its true utility, and utilities are defined on [0,1]^m
--   - reading: the optimum (of player i) → U_i(1), the utility of the bundle of all goods; reason: the proof (pp. 30–31) bounds against u_i(1)
--   - reading: Nash equilibrium → pure Nash equilibrium; reason: §2 defines the equilibria considered as pure; the proofs on pp. 30–31 start from a pure equilibrium
--   - encoding: strictly increasing → strictly monotone on the box in the product order; reason: the paper's order notion (Appendix D.3)
--   - encoding: the Trading Post allocation x_{i,j} = b_{i,j}/Σ_k b_{k,j} if b_{i,j} > 0, else 0 (p. 12) → the base allocation of TP(0), whose effective bids equal the bids for every b ≥ 0; reason: the same allocation on every strategy profile
--   - reading: a mechanism returning a market equilibrium for each admissible concave report → a total equilibrium-valued rule on all admissible concave profiles; reason: restores the source premise; the partial-rule draft could suppress truthful deviations when their reported markets have no equilibrium. Existence of such a total rule is not asserted; where none exists, this universal conditional is vacuous, as is the source specification
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 17, Theorem 5.1; proof pp. 30–31 (Appendix E)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_5_1 :
    (∀ (n m : ℕ) (I : Instance n m), GenStanding I →
      ∀ U : Fin n → (Fin m → ℝ) → ℝ, (∀ i, IsConcaveUtility (U i)) →
      ∀ O : (Fin n → (Fin m → ℝ) → ℝ) → (Fin m → ℝ) × (Fin n → Fin m → ℝ),
        IsOutcomeRule IsConcaveUtility (concaveMarketEq I) O →
        ∀ W : Fin n → (Fin m → ℝ) → ℝ, IsMechPNE IsConcaveUtility (concaveMarketEq I) U O W →
          ∀ i, I.B i / totalBudget I * U i 1 ≤ U i ((O W).2 i)) ∧
    (∀ (n m : ℕ) (I : Instance n m), GenStanding I →
      ∀ U : Fin n → (Fin m → ℝ) → ℝ, (∀ i, IsConcaveUtility (U i)) →
      (∀ i, StrictMonoOn (U i) (box m)) →
      ∀ b : Fin n → Fin m → ℝ, IsPNEU I U 0 b →
        ∀ i, I.B i / totalBudget I * U i 1 ≤ U i (tpAlloc 0 b i)) ∧
    (∀ (n m : ℕ) (I : Instance n m), GenStanding I →
      ∀ U : Fin n → (Fin m → ℝ) → ℝ, (∀ i, IsConcaveUtility (U i)) →
      (∀ i, StrictMonoOn (U i) (box m)) →
      ∀ Δ : ℝ, 0 < Δ → Δ < 1 / (m : ℝ) →
      ∀ b : Fin n → Fin m → ℝ, IsPNEU I U Δ b →
        ∀ i, I.B i / totalBudget I * (1 - Δ * ((m : ℝ) - 1) / I.B i) * U i 1 ≤
          U i (tpAlloc Δ b i)) := by sorry

end TradingPostNSW.Leontief.Supplement
