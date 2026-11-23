-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_theorem_EC_1
-- name    : SuspensionContract.HighCostC2.Supplement.theorem_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:17:01.971735+00:00
-- url     : https://prove2.me/theorems/60f78dea-4aec-4088-a87d-03bc15eb3d4f
-- title:
--   Theorem EC.1 (corrected: deterministic controls and endpoint conventions)
-- statement:
--   Let $r=\rho$ and $K\ge0$, retaining the rate, effort, cost and revenue assumptions. The equal-discount function $V_e$ solves (EC.15) with $V_e(0)=\underline v$ and its prescribed constant extension; the solution is unique on nonnegative utility. Never hiring is feasible and has value $\underline v$.
--
--   Both cost branches are retained:
--   $$K\ge\bar K_e\ \Longrightarrow\ (V_e,\underline v)\text{ satisfies (20)–(22)},$$
--   $$K<\bar K_e\ \Longrightarrow\ (V_e,V_\emptyset)\text{ satisfies (20)–(22)},$$
--   where $V_\emptyset$ is (EC.17), with its actual tangent pair. In the latter branch, if $V_e'(\bar\theta^K)>1$, then for every $w\ge\bar\theta^K$ a feasible contract exists and
--   $$U(\Gamma^*(w;0,0,\bar w,\bar w))=V_\emptyset(w)-w.$$
--   The unbounded initial-utility quantifier includes $w>\bar w$: the excess is transferred at time zero as in endnote 7. Zero cost uses the limiting tangent at zero. The equal-rate ODE is not obtained by substituting into the main-text truncated cutoff selector.
--
--   Differences from the source:
--   - correction: D is called deterministic but only F-adaptedness is written. → The public filtration after initialization contains no noise beyond N and Q.; reason: Adaptedness alone admits an independent Poisson D and falsifies the two-noise PK equation; this implements the intended deterministic control. See DISPROOF.md.
--   - reading: (20) is printed at w≥0 with a left-derivative convention. → The published OptCond uses (20) at w>0 and retains (21),(22) at zero.; reason: The left derivative at the endpoint does not exist and positive-power suspension values can have infinite right slope there; this is the series boundary convention.
--   - reading: EC.15 prints an extra p in its delayed argument and EC.17 stops its displayed domain at wbar. → Use min(w+β,wbar) and continue Vempty constantly beyond wbar; include K=0 with the limiting tangent convention.; reason: Equation (25), the constant extension of Ve and EC.1.3 fix these readings; endnote 7 supplies the initial transfer for unbounded w.
--   - encoding: Processes and equations are written without null-set conventions. → Utilities are actual conditional expectations; drift statements use predictable versions dt-a.e., jump statements use indistinguishable versions.; reason: This gives the standard stochastic interpretation and preserves all right-continuous binary deviations, both contract states and the infinite time horizon.
--   - generalization: Theorem EC.1 cites the existence and uniqueness of V_e and of the tangent pair from Sun–Tian (2018) and Lemma 4. → Existence/uniqueness of the EC.15 solution, existence of a feasible never-hire contract and of the tangent pair are additional conclusions.; reason: These are the governing facts the theorem's displayed objects rely on (ec6); dropping them gives the printed theorem.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. ec7, Theorem EC.1

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_EqualRates

namespace SuspensionContract.HighCostC2.Supplement

theorem theorem_EC_1 (P : Params) (hP : NonnegativeCostStanding P) (hequal : P.r = P.ρ) :
    EqualSolution P (equalValue P) ∧
    (∀ f, EqualSolution P f → ∀ w : ℝ, 0 ≤ w → f w = equalValue P w) ∧
    (∃ G : Contract, IsNeverHire P G ∧ Feasible P G) ∧
    (∀ G : Contract, IsNeverHire P G → principalUtility P G = (P.vlow : EReal)) ∧
    (equalThreshold P ≤ P.K → P.OptCond (equalValue P) (fun _ => P.vlow)) ∧
    (P.K < equalThreshold P →
      EqualTangent P (equalTangentPair P).1 (equalTangentPair P).2 ∧
      P.OptCond (equalValue P) (equalSuspension P) ∧
      (1 < equalDeriv P (equalTangentPair P).1 →
        ∀ w : ℝ, (equalTangentPair P).1 ≤ w →
          (∃ G : Contract, IsBandContract P (alwaysBand P) w G ∧ Feasible P G) ∧
          (∀ G : Contract, IsBandContract P (alwaysBand P) w G →
            principalUtility P G = ((equalSuspension P w - w : ℝ) : EReal)))) := by sorry

end SuspensionContract.HighCostC2.Supplement
