-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_theorem_2
-- name    : SuspensionContract.HighCostC2.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:08:59.807812+00:00
-- url     : https://prove2.me/theorems/2363c2d1-29f8-44ae-a3d9-2b4ba31273fc
-- title:
--   Theorem 2 (corrected: zero-threshold plateau and strict-discount construction)
-- statement:
--   Fix arrival, cost and discount primitives satisfying the standing assumptions, with $r<\rho$. The high-cost threshold $\bar K(R)$ is nondecreasing in revenue per arrival on $R\Delta\mu>c$. It is strictly increasing on the region where its value is positive; a zero-threshold plateau is possible. If $\mu<\rho-r$, the corrected threshold $\underline K(R)$ is non-increasing for $R\ge\hat R$.
--
--   All three contract regimes are retained:
--   $$K>\bar K\ \Longrightarrow\ \underline\Gamma\text{ is optimal},$$
--   $$\mu<\rho-r,\ R\ge\hat R,\ \underline K\le K\le\bar K\ \Longrightarrow\ \bar\Gamma\text{ is optimal}.$$
--   In every remaining case there are thresholds and an initial utility for an optimal Definition 1 contract, with
--   $$0<\underline\theta\le\check w<\bar\theta<\hat w\le\bar w.$$
--   Optimality includes feasibility and comparison against every feasible stochastic contract. The closed upper endpoint of the always-work interval and the source's remaining-case quantifiers are preserved; initial utility may be zero as allowed in Definition 1.
--
--   Differences from the source:
--   - correction: D is called deterministic but only F-adaptedness is written. → The public filtration after initialization contains no noise beyond N and Q.; reason: Adaptedness alone admits an independent Poisson D and falsifies the two-noise PK equation; this implements the intended deterministic control. See DISPROOF.md.
--   - correction: The main text allows r≤ρ while its cutoff construction is defined on wtil<wbar. → The main-text threshold results bind r<ρ; Theorem EC.1 separately retains r=ρ and K≥0.; reason: At equal rates every truncated DDE solution is constant and no Lemma-3 cutoff in [0,wbar) exists; EC.1.3 uses a different endpoint ODE. No printed case is silently identified with a junk infimum.
--   - correction: The bracket in (33) contains (r/ρ)β. → The imported published Klow uses ((ρ−μ)/ρ)β.; reason: The proof identifies this threshold with (EC.69), giving the corrected term; the regime is not narrowed for proof convenience.
--   - correction: Theorem 2 calls Kbar(R) increasing, strictly by endnote 8. → Kbar is nondecreasing on the full revenue domain and strictly increasing where it is positive.; reason: For r=1, rho=2, mu=1/2, mulow=0, b=c=1, the distinct revenues 741/256 and 767/243 both give Kbar1=0. The exact DDE calculation is retained in DISPROOF.md.
--   - encoding: Processes and equations are written without null-set conventions. → Utilities are actual conditional expectations; drift statements use predictable versions dt-a.e., jump statements use indistinguishable versions.; reason: This gives the standard stochastic interpretation and preserves all right-continuous binary deviations, both contract states and the infinite time horizon.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. 16–17, Theorem 2

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Regimes

namespace SuspensionContract.HighCostC2.Supplement

open Set

theorem theorem_2 (P : Params) (hP : P.Standing) (hdiscount : P.r < P.ρ) :
    MonotoneOn (fun R => highThreshold (withRevenue P R)) (RevenueDomain P) ∧
    StrictMonoOn (fun R => highThreshold (withRevenue P R))
      {R | R ∈ RevenueDomain P ∧ 0 < highThreshold (withRevenue P R)} ∧
    (P.μ < P.ρ - P.r →
      AntitoneOn (fun R => (toAW (withRevenue P R)).Klow) (Ici P.Rhat)) ∧
    (highThreshold P < P.K →
      ∃ G : Contract, IsNeverHire P G ∧ IsOptimal P G) ∧
    (P.Condition2 ∧ (toAW P).Klow ≤ P.K ∧ P.K ≤ highThreshold P →
      ∃ G : Contract, IsAlwaysWork P G ∧ IsOptimal P G) ∧
    (¬highThreshold P < P.K ∧
      ¬(P.Condition2 ∧ (toAW P).Klow ≤ P.K ∧ P.K ≤ highThreshold P) →
      ∃ (B : Band) (w : ℝ) (G : Contract),
        0 < B.thLo ∧ B.thLo ≤ B.wLo ∧ B.wLo < B.thHi ∧ B.thHi < B.wHi ∧
        B.wHi ≤ P.wbar ∧ B.InitialDomain w ∧ IsBandContract P B w G ∧ IsOptimal P G) := by sorry

end SuspensionContract.HighCostC2.Supplement
