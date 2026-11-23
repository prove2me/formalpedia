-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_lemma_1
-- name    : SuspensionContract.HighCostC2.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:06:59.891987+00:00
-- url     : https://prove2.me/theorems/cc778e8b-13d6-4182-92b9-3bd616885d33
-- title:
--   Lemma 1 (corrected: exclude instantaneous positive suspension cycles)
-- statement:
--   Take the weakly ordered thresholds of Definition 1,
--   $$0\le\underline\theta\le\check w\le\bar\theta\le\hat w\le\bar w,$$
--   For each $w_0\in\{0\}\cup[\check w,\hat w]$, require either $w_0=0$, $w_0=\hat w=\bar w$, $\bar\theta=0$, or $\underline\theta<\bar\theta$. Then the event equations construct a feasible contract, and every such realization delivers precisely
--   $$u(\Gamma^*(w_0;\underline\theta,\check w,\bar\theta,\hat w),\bar\nu)=w_0.$$
--   The account in the construction is independent of the conditional-utility definition, so the identity has mathematical content. Initial utility zero and all-zero termination thresholds are retained.
--
--   Differences from the source:
--   - correction: D is called deterministic but only F-adaptedness is written. → The public filtration after initialization contains no noise beyond N and Q.; reason: Adaptedness alone admits an independent Poisson D and falsifies the two-noise PK equation; this implements the intended deterministic control. See DISPROOF.md.
--   - correction: Lemma 1 permits all four positive thresholds to coincide. → Require w0=0, or w0=wHi=wbar, or barTheta=0, or lowerTheta<barTheta; zero utility remains absorbing.; reason: With all thresholds equal a>0, (14) demands switches throughout an event-free interval; no locally finite switching process exists. See DISPROOF.md.
--   - encoding: Processes and equations are written without null-set conventions. → Utilities are actual conditional expectations; drift statements use predictable versions dt-a.e., jump statements use indistinguishable versions.; reason: This gives the standard stochastic interpretation and preserves all right-continuous binary deviations, both contract states and the infinite time horizon.
--   - generalization: Lemma 1 asserts only the utility identity (17) for the contract of Definition 1. → Also asserts that the event equations admit a realization in the contract class C.; reason: Definition 1 constructs Γ* and the paper treats it as a member of C; the existence clause specializes away by dropping it.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. 15, Lemma 1

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_BandContracts

namespace SuspensionContract.HighCostC2.Supplement

theorem lemma_1 (P : Params) (hP : P.Standing) (B : Band) (hB : B.Ordered P) :
    ∀ w : ℝ, B.InitialDomain w →
      (w = 0 ∨ (w = P.wbar ∧ B.wHi = P.wbar) ∨ B.NoInstantCycle) →
      (∃ G : Contract, IsBandContract P B w G ∧ Feasible P G) ∧
      ∀ G : Contract, IsBandContract P B w G →
        agentUtility P G (complying P G) = (w : EReal) := by sorry

end SuspensionContract.HighCostC2.Supplement
