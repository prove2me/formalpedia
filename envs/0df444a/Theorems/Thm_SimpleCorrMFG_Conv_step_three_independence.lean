-- Prove2me | Theorems.Thm_SimpleCorrMFG_Conv_step_three_independence
-- name    : SimpleCorrMFG.Conv.step_three_independence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:30.21636+00:00
-- url     : https://prove2.me/theorems/6df5f75a-efd1-4f80-8597-0611d28eaf59
-- title:
--   Proof of Theorem 6.1, Step Three, p. 23 — $X_1^N(0)$, $\xi_1^N(\cdot)$ and $(\Phi_1^N,\hat\mu_1^N(\cdot))$ are independent
-- statement:
--   Let $N\ge2$, let the initial states be i.i.d., $\mathfrak m^N=\otimes^N m$ for some $m\in\mathcal P(\mathcal X)$, let $\gamma^N$ be any correlated profile, and assume $\Psi$ measurable (and $f,F$ bounded measurable). On the canonical $N$-player space, with $\hat\mu_1^N(t)=(N-1)^{-1}\sum_{l=2}^N\delta_{\hat X_l^N(t)}$ the measure (6.1) of the decoupled system, the three random elements
--   $$X_1^N(0),\qquad \xi_1^N(\cdot)=(\xi_1^N(1),\dots,\xi_1^N(T)),\qquad \big(\Phi_1^N,\hat\mu_1^N(0),\dots,\hat\mu_1^N(T)\big)$$
--   are independent.
--
--   Passing to the limit, this gives the independence property (c) required of a realization of the mean field game, even though $\Phi_1^N$ and the empirical flow are correlated.
--
--   **Formalization Note** Mutual independence of the three is stated as the two pairwise statements $X_1(0)\perp(\xi_1,(\Phi_1,\hat\mu_1))$ and $\xi_1\perp(\Phi_1,\hat\mu_1)$, which together are equivalent to it.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, p. 23 (proof of Theorem 6.1, end of Step Three)

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer
import Definitions.Def_SimpleCorrMFG_Conv_Coupling

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval Filter Topology

/-- Proof of Theorem 6.1, Step Three (p. 23): when the initial states are i.i.d. (as under (A5)),
`X_1(0)`, `ξ_1(·)` and `(Φ_1, μ̂_1(·))` are independent, for every `N ≥ 2`. Mutual independence of
the three is stated as `X_1(0) ⫫ (ξ_1(·), (Φ_1, μ̂_1(·)))` and `ξ_1(·) ⫫ (Φ_1, μ̂_1(·))`. -/
theorem step_three_independence {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [TopologicalSpace X] [DiscreteTopology X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Fintype Γ] [Nonempty Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MeasurableSpace Γ]
    [DiscreteMeasurableSpace Γ]
    (M : Model T X Γ) (hM : M.Standing) {N : ℕ} [NeZero N] (hN : 2 ≤ N) (m : Meas X)
    (γ : ProbabilityMeasure (Fin N → Strat T X Γ)) :
    IndepFun (fun ω : NOmega T N X Γ => ω.1 0)
        (fun ω => ((fun t => ω.2.2 t 0), (ω.2.1 0, fun t => hatEmp M ω t)))
        (nLaw (prodInit N m) γ) ∧
      IndepFun (fun ω : NOmega T N X Γ => fun t => ω.2.2 t 0)
        (fun ω => (ω.2.1 0, fun t => hatEmp M ω t)) (nLaw (prodInit N m) γ) := by sorry

end SimpleCorrMFG.Conv
