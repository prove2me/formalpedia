-- Prove2me | Theorems.Thm_ShapiroSDDP_Convergence_lower_bound
-- name    : ShapiroSDDP.Convergence.lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:13.109602+00:00
-- url     : https://prove2.me/theorems/1545549a-b0fa-4539-a875-e468208227e5
-- title:
--   §3, p. 8 — the optimal value ϑ_k of (3.13) at iteration k is at most the optimal value of the SAA problem
-- statement:
--   Under the assumptions of the cut-validity statement (finite-valued cost-to-go functions on reachable decisions, valid initial cuts, any run of the SDDP method), let $\underline\vartheta_k$ be the optimal value of the first-stage problem (3.13) at iteration $k$,
--   $$\underline\vartheta_k=\inf\big\{c_1^\top x_1+\mathfrak Q_2(x_1):\ A_1x_1=b_1,\ x_1\ge0\big\}.$$
--   If $\underline\vartheta_k$ is finite, then
--   $$\underline\vartheta_k\le\min\big\{c_1^\top x_1+\widetilde{\mathcal Q}_2(x_1):\ A_1x_1=b_1,\ x_1\ge0\big\},$$
--   the optimal value (3.7) of the SAA problem.
--
--   This is the lower bound reported by the algorithm at each iteration.
--
--   **Formalization Note** $\underline\vartheta_k$ is the infimum of the LP (3.13) in epigraph form with the iteration-$k$ stage-1 cut set; it is genuine because the hypothesis states that this LP is feasible and bounded below. The optimal value (3.7) is then also a genuine infimum.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, p. 8, §3, after (3.13)

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model
import Definitions.Def_ShapiroSDDP_Convergence_SDDP

namespace ShapiroSDDP.Convergence

/-- §3, p. 8: along every run, the optimal value `ϑ_k` of problem (3.13) at iteration `k`, whenever
it is finite, is at most the optimal value (3.7) of the SAA problem. -/
theorem lower_bound (I : Instance) (hfin : FiniteValued I) (C₀ : (t : ℕ) → Finset (Cut I t))
    (hC₀ : ValidInit I C₀) (sol : Oracle I) {M : ℕ} (ω : ℕ → Fin M → Scen I)
    (cuts : ℕ → (t : ℕ) → Finset (Cut I t)) (hrun : IsRun I C₀ sol ω cuts) (k : ℕ)
    (hk : CutLPFinite I.A₁ I.b₁ (cuts k 1) I.c₁) :
    cutLPVal I.A₁ I.b₁ (cuts k 1) I.c₁ ≤ optVal I := by sorry

end ShapiroSDDP.Convergence
