-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_theorem_3
-- name    : SuspensionContract.HighCostC2.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:10:07.829174+00:00
-- url     : https://prove2.me/theorems/1a2e6866-ab90-4d14-ba1f-9c4c02b0740c
-- title:
--   Theorem 3 (corrected: strict-discount main-text threshold)
-- statement:
--   Under the standing assumptions and $r<\rho$, let $\bar K$ be $\bar K_1$ in Condition 1 and $\bar K_2$ in Condition 2. Then
--   $$K\ge\bar K\quad\Longrightarrow\quad\underline\Gamma\text{ is optimal},\qquad U(\underline\Gamma)=\underline v.$$
--   An actual feasible never-hire realization exists, and every realization is optimal over the complete contract class. In particular equality at the threshold is included.
--
--   Differences from the source:
--   - correction: D is called deterministic but only F-adaptedness is written. → The public filtration after initialization contains no noise beyond N and Q.; reason: Adaptedness alone admits an independent Poisson D and falsifies the two-noise PK equation; this implements the intended deterministic control. See DISPROOF.md.
--   - correction: The main text allows r≤ρ while its cutoff construction is defined on wtil<wbar. → The main-text threshold results bind r<ρ; Theorem EC.1 separately retains r=ρ and K≥0.; reason: At equal rates every truncated DDE solution is constant and no Lemma-3 cutoff in [0,wbar) exists; EC.1.3 uses a different endpoint ODE. No printed case is silently identified with a junk infimum.
--   - encoding: Processes and equations are written without null-set conventions. → Utilities are actual conditional expectations; drift statements use predictable versions dt-a.e., jump statements use indistinguishable versions.; reason: This gives the standard stochastic interpretation and preserves all right-continuous binary deviations, both contract states and the infinite time horizon.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. 24, Theorem 3

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Regimes

namespace SuspensionContract.HighCostC2.Supplement

theorem theorem_3 (P : Params) (hP : P.Standing) (hdiscount : P.r < P.ρ)
    (hK : highThreshold P ≤ P.K) :
    (∃ G : Contract, IsNeverHire P G ∧ IsOptimal P G ∧ principalUtility P G = (P.vlow : EReal)) ∧
    (∀ G : Contract, IsNeverHire P G → Feasible P G ∧ IsOptimal P G ∧
      principalUtility P G = (P.vlow : EReal)) := by sorry

end SuspensionContract.HighCostC2.Supplement
