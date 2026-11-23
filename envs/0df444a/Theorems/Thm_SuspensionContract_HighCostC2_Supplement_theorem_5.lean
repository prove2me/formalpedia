-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_theorem_5
-- name    : SuspensionContract.HighCostC2.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:13:35.799472+00:00
-- url     : https://prove2.me/theorems/997df46c-35a2-49a6-8c97-0027222c76dd
-- title:
--   Theorem 5 (corrected: strict-discount canonical control-band branch)
-- statement:
--   Under Condition 3 with $r<\rho$, use the canonical Proposition 6 parameters and the value function $V_\emptyset$ of (46). A maximizer exists in the entire interval
--   $$w_0^*\in[\bar\vartheta,\hat{\mathbf w}],\qquad V_\emptyset(w)-w\le V_\emptyset(w_0^*)-w_0^*\quad(w\ge0).$$
--   The corresponding contract (47) is feasible and globally optimal, and it attains
--   $$U(\hat\Gamma(w_0^*))=V_\emptyset(w_0^*)-w_0^*.$$
--   Both Condition 3 branches are included. The construction retains random switching when $\underline\vartheta<\check w(\hat{\mathbf w})$ and deterministic switching otherwise. The source's maximizer is established, not introduced as an existence hypothesis.
--
--   Differences from the source:
--   - correction: D is called deterministic but only F-adaptedness is written. → The public filtration after initialization contains no noise beyond N and Q.; reason: Adaptedness alone admits an independent Poisson D and falsifies the two-noise PK equation; this implements the intended deterministic control. See DISPROOF.md.
--   - correction: The main text allows r≤ρ while its cutoff construction is defined on wtil<wbar. → The main-text threshold results bind r<ρ; Theorem EC.1 separately retains r=ρ and K≥0.; reason: At equal rates every truncated DDE solution is constant and no Lemma-3 cutoff in [0,wbar) exists; EC.1.3 uses a different endpoint ODE. No printed case is silently identified with a junk infimum.
--   - correction: The bracket in (33) contains (r/ρ)β. → The imported published Klow uses ((ρ−μ)/ρ)β.; reason: The proof identifies this threshold with (EC.69), giving the corrected term; the regime is not narrowed for proof convenience.
--   - encoding: Processes and equations are written without null-set conventions. → Utilities are actual conditional expectations; drift statements use predictable versions dt-a.e., jump statements use indistinguishable versions.; reason: This gives the standard stochastic interpretation and preserves all right-continuous binary deviations, both contract states and the infinite time horizon.
--   - generalization: Theorem 5 asserts that Γ̂(w₀*) is optimal for a maximizer w₀*∈[ϑ̄,𝐰̂]. → Also asserts, for every maximizer in [ϑ̄,𝐰̂] and every realization, optimality and U=V_∅(w)−w.; reason: The existential first clause is the printed theorem; the universal clause adds (48) at the maximizer.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. 28, Theorem 5

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Regimes

namespace SuspensionContract.HighCostC2.Supplement

open Set

theorem theorem_5 (P : Params) (hP : P.Standing) (hdiscount : P.r < P.ρ)
    (hC : (toCB P).Condition3) :
    (∃ w ∈ Icc (optimalBand P).thHi (optimalBand P).wHi,
      (∀ x : ℝ, 0 ≤ x → bandSuspensionValue P x - x ≤ bandSuspensionValue P w - w) ∧
      ∃ G : Contract, IsBandContract P (optimalBand P) w G ∧ IsOptimal P G) ∧
    (∀ w ∈ Icc (optimalBand P).thHi (optimalBand P).wHi,
      (∀ x : ℝ, 0 ≤ x → bandSuspensionValue P x - x ≤ bandSuspensionValue P w - w) →
      ∀ G : Contract, IsBandContract P (optimalBand P) w G → IsOptimal P G ∧
        principalUtility P G = ((bandSuspensionValue P w - w : ℝ) : EReal)) := by sorry

end SuspensionContract.HighCostC2.Supplement
