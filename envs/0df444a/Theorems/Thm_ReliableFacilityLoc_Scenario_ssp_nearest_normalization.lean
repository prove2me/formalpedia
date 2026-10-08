-- Prove2me | Theorems.Thm_ReliableFacilityLoc_Scenario_ssp_nearest_normalization
-- name    : ReliableFacilityLoc.Scenario.ssp_nearest_normalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:59.139436+00:00
-- url     : https://prove2.me/theorems/a22f92c6-1865-4268-8c37-0bbb0fdbe468
-- title:
--   An optimal (SSP) solution may serve every customer by her nearest operating open facility
-- statement:
--   Let $(X,Y)$ be an optimal solution of (SSP). Then there is an assignment $Y'$ such that $(X,Y')$ is also optimal for (SSP) and, for every customer $i$, scenario $\omega$ and facility $k$,
--   $$Y'_{ik\omega} = 1 \iff k = \min\{0 \le k \le J : \delta_{k\omega}X_k = 1,\ d_{ik} \le d_{ik'}\ \forall k' \ne k \text{ with } \delta_{k'\omega}X_{k'} = 1\},$$
--   with the conventions $\delta_{J\omega} = 1$ and $X_J = 1$. In words: each customer is always served by her closest open, operating facility, and ties are broken in favour of the lowest index.
--
--   This is the "without loss of generality" step of the second half of the proof of Proposition 1.
--
--   **Formalization Note** The "without loss of generality" is stated as the existence of such a $Y'$ for the same location vector $X$. It relies on $\lambda_i \ge 0$; no sign is needed on $d$ or $\phi$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), Appendix A.1 (proof of Proposition 1), p. 33 (PDF 35), "Without loss of generality, we assume that Y_ijω = 1 if and only if …"

import Definitions.Def_ReliableFacilityLoc_Scenario_SSP

open Finset

namespace ReliableFacilityLoc.Scenario

/-- **Nearest-open-facility normalization of (SSP)** (Cui–Ouyang–Shen, UCTC-FR-2010-02 (Feb. 2010),
A.1, proof of Proposition 1, p. 33 (PDF 35)): "Without loss of generality, we assume that
`Y_ijω = 1` if and only if `j = min{0 ≤ k ≤ J : δ_kω X_k = 1, d_ik ≤ d_ik' ∀ k' ≠ k s.t.
δ_k'ω X_k' = 1}` (by convention, we assume `X_J = 1`)". For every optimal `(X, Y)` of (SSP) there is
an optimal `(X, Y')` of (SSP), with the same `X`, in which every customer in every scenario is
served by her closest operating open facility, ties broken by the lowest index.

Formalization Note: the "without loss of generality" is stated as the existence of such a `Y'`
for the same `X`. It uses `λ_i ≥ 0` (part of `Instance`); no sign is needed on `d` or `φ`. -/
theorem ssp_nearest_normalization {I J R : ℕ} (D : Instance I J R) (X : Fin J → ℝ)
    (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ) (h : D.IsSSPOptimal X Y) :
    ∃ Y' : Fin I → Fin (J + 1) → FailureScenario J → ℝ,
      D.IsSSPOptimal X Y' ∧ ∀ i ω k, Y' i k ω = 1 ↔ D.IsNearestServer X i ω k := by sorry

end ReliableFacilityLoc.Scenario
