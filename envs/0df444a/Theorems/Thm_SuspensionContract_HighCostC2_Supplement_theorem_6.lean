-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_theorem_6
-- name    : SuspensionContract.HighCostC2.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:15:37.578369+00:00
-- url     : https://prove2.me/theorems/21ade666-6268-4f02-a117-dd0a8006bb49
-- title:
--   Theorem 6 (corrected: nondegenerate strict-discount zero-cost model)
-- statement:
--   In the same fixed-primitive limiting regime as Proposition 8, there exist finite real numbers $\hat{\mathbf w}^0,c^0$ with
--   $$\hat{\mathbf w}(K)\longrightarrow\hat{\mathbf w}^0,\qquad\mathsf c(K)\longrightarrow c^0\quad(K\downarrow0).$$
--   Using the common switching-threshold limit $\theta_0$ and the entire piecewise function of Theorem 6,
--   $$V_I=V_\emptyset=\mathbb V_{\theta_0}$$
--   satisfies every clause of (20)–(22) with switching cost exactly zero. The two finite limits are conclusions, and the certificate covers all nonnegative utility, with generator inequalities at positive utility under the shared boundary convention. No positive-cost standing assumption is imposed at the limiting model.
--
--   Differences from the source:
--   - correction: The main text allows r≤ρ while its cutoff construction is defined on wtil<wbar. → The main-text threshold results bind r<ρ; Theorem EC.1 separately retains r=ρ and K≥0.; reason: At equal rates every truncated DDE solution is constant and no Lemma-3 cutoff in [0,wbar) exists; EC.1.3 uses a different endpoint ODE. No printed case is silently identified with a junk infimum.
--   - correction: The bracket in (33) contains (r/ρ)β. → The imported published Klow uses ((ρ−μ)/ρ)β.; reason: The proof identifies this threshold with (EC.69), giving the corrected term; the regime is not narrowed for proof convenience.
--   - reading: (20) is printed at w≥0 with a left-derivative convention. → The published OptCond uses (20) at w>0 and retains (21),(22) at zero.; reason: The left derivative at the endpoint does not exist and positive-power suspension values can have infinite right slope there; this is the series boundary convention.
--   - reading: The theorem varies K down to zero under Condition 3. → Use a cost-free admissibility predicate, a positive branch bound, and evaluate the published OptCond at K=0.; reason: The published Standing includes K>0 and cannot be assumed at the limit; EC.4.2 states the positive branch bounds explicitly.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. 29, Theorem 6

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Limits

open scoped NNReal

namespace SuspensionContract.HighCostC2.Supplement

open Filter Set
open scoped Topology

theorem theorem_6 (P : SuspensionContract.ControlBand.Params)
    (hP : CostFreeStanding P) (hdiscount : P.r < P.ρ) (hregime : ZeroCostRegime P) :
    ∃ w0 c0 : ℝ,
      Tendsto (workingCutoff P) (nhdsWithin 0 (Ioi 0)) (𝓝 w0) ∧
      Tendsto (bandCoefficient P) (nhdsWithin 0 (Ioi 0)) (𝓝 c0) ∧
      (withCost P 0).OptCond (zeroValue P w0 c0) (zeroValue P w0 c0) := by sorry

end SuspensionContract.HighCostC2.Supplement
