-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_proposition_8
-- name    : SuspensionContract.HighCostC2.Supplement.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:14:49.629838+00:00
-- url     : https://prove2.me/theorems/0a7ec8d5-39f7-462c-a85e-c69c98ae1299
-- title:
--   Proposition 8 (corrected: nondegenerate strict-discount limit regime)
-- statement:
--   Fix every primitive except switching cost, with $r<\rho$, and suppose Condition 1 with $\bar K_1>0$ or Condition 2 with $\underline K>0$. On the complete positive-cost Condition 3 interval, the canonical lower threshold is strictly decreasing and the upper threshold strictly increasing. Both converge to the same finite real turning point:
--   $$\lim_{K\downarrow0}\underline\vartheta(K)=\theta_0=\lim_{K\downarrow0}\bar\vartheta(K).$$
--   The limits are through all positive costs approaching zero, not merely a sequence. The turning point is identified by the proof in EC.4.1, and is independent of switching cost.
--
--   Differences from the source:
--   - correction: The main text allows r≤ρ while its cutoff construction is defined on wtil<wbar. → The main-text threshold results bind r<ρ; Theorem EC.1 separately retains r=ρ and K≥0.; reason: At equal rates every truncated DDE solution is constant and no Lemma-3 cutoff in [0,wbar) exists; EC.1.3 uses a different endpoint ODE. No printed case is silently identified with a junk infimum.
--   - correction: The bracket in (33) contains (r/ρ)β. → The imported published Klow uses ((ρ−μ)/ρ)β.; reason: The proof identifies this threshold with (EC.69), giving the corrected term; the regime is not narrowed for proof convenience.
--   - reading: Condition 3 is stated for a positive cost, followed by K↓0. → Fix the other primitives and require the branch cost bound to be positive.; reason: This is exactly the nonempty limiting regime spelled out in EC.4.1; the hypothesis does not assert either limit.
--   - generalization: Proposition 8 asserts that the two limits exist and coincide, naming the common value θ₀. → The common limit is identified with the explicit turning point θ̲⁰ of the construction.; reason: EC.4.1 (ec50) identifies θ₀=θ̲⁰; forgetting the value gives the printed statement.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. 29, Proposition 8

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Limits

open scoped NNReal

namespace SuspensionContract.HighCostC2.Supplement

open Filter Set
open scoped Topology

theorem proposition_8 (P : SuspensionContract.ControlBand.Params)
    (hP : CostFreeStanding P) (hdiscount : P.r < P.ρ) (hregime : ZeroCostRegime P) :
    StrictAntiOn (lowerTheta P) (BandCosts P) ∧
    StrictMonoOn (upperTheta P) (BandCosts P) ∧
    Tendsto (lowerTheta P) (nhdsWithin 0 (Ioi 0)) (𝓝 (limitTheta P)) ∧
    Tendsto (upperTheta P) (nhdsWithin 0 (Ioi 0)) (𝓝 (limitTheta P)) := by sorry

end SuspensionContract.HighCostC2.Supplement
