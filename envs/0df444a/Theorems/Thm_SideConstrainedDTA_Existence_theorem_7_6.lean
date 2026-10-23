-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_theorem_7_6
-- name    : SideConstrainedDTA.Existence.theorem_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:30.40506+00:00
-- url     : https://prove2.me/theorems/a74df34e-b3b6-4a41-9dc8-9c13466f5e66
-- title:
--   Theorem 7.6 (with DTC), p. 39 — under (A2), (A3), (A5), (A9)–(A19) and continuous capacities (A22), a strong MNSDE that is also a strong LPDE exists
-- statement:
--   Consider a dynamic traffic network with departure time choice: finitely many commodities and walks, a horizon $[t_0,t_f]$, flow volumes $Q_i$, inflow bounds $B_p$, an effective walk delay operator $\Psi$, arrival times $\tau^j_p(h,t)$, edge loads $f_e(h,\theta)$ and edge capacities $c_e(\theta)$. Let $S=\{h\in\Lambda(Q)\mid f_e(h,\theta)\le c_e(\theta)\ \forall e,\theta\ge0\}$ be the capacity-feasible inflows (23). Assume the standing model and
--
--   1. (A2) every commodity has a walk; (A3) $\Lambda(Q)\ne\emptyset$; (A5) $\Psi_p(h,\cdot)$ is continuous for $h\in S$;
--   2. (A9) no capacity violation at time $0$; (A10) an outside option exists for every inflow and commodity; (A11)–(A12) capacities are non-negative and non-decreasing;
--   3. (A13)–(A16) continuity of edge loads, uniform convergence of edge loads and arrival times along weakly convergent inflows, and the principle of causation;
--   4. (A17) arrival times along a common prefix do not depend on the rest of the walk; (A18) $\Psi$ is continuous and weak-uniformly continuous; (A19) $\Psi$ is uniformly bounded on $S$;
--   5. (A22) every capacity $c_e$ is continuous on $\mathbb R_{\ge0}$.
--
--   Then there is a walk inflow $h^*$ that is both a **strong dynamic Marcotte–Nguyen–Schoeb equilibrium** and a **strong dynamic Larsson–Patriksson equilibrium**: $h^*\in S$ and
--   $$\Psi_p(h^*,t)\le\Psi_q(h^*,t+\Delta)\qquad\text{for all walks }p,\ t\in[t_0,t_f],\ (q,\Delta)\in U_p(h^*,t),$$
--   where $U_p$ is formed from the deviation sets (26), and also from (24).
--
--   This is the first existence result for dynamic equilibria under hard edge-load capacities, a setting in which the feasible set is non-convex and variational-inequality methods do not apply directly.
--
--   **Formalization Note.** Only the case with departure time choice is posed; the case with fixed inflow rates is not. (A22) is added; the theorem in the paper does not assume it, but two steps of its proof on pp. 40–41 need it, and the paper assumes it in Theorem 7.9. (A17) is posed for every $h\in\Lambda(Q)$ instead of $h\in S$, and measurability of the arrival times is a standing convention. One flow is required to be both equilibria at once, which implies the two separate existence claims. Node indices are 0-based (`tau h p j t` is $\tau^{j+1}_p(h,t)$).
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 39, Theorem 7.6 (case with DTC); assumptions pp. 38–39; (A22) p. 45

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Theorem 7.6 (with DTC), p. 39: under (A2), (A3), (A5), (A9)–(A19) and continuous capacities
(A22), there is a walk inflow that is both a strong MNSDE and a strong LPDE. -/
theorem theorem_7_6 {I W E : Type*} [Fintype I] [Fintype W] [Fintype E] [DecidableEq I]
    [DecidableEq W] [DecidableEq E] (N : Model I W E) (hN : N.Standing)
    (h2 : A2 N) (h3 : A3 N) (h5 : A5 N) (h9 : A9 N) (h10 : A10 N) (h11 : A11 N) (h12 : A12 N)
    (h13 : A13 N) (h14 : A14 N) (h15 : A15 N) (h16 : A16 N) (h17 : A17 N) (h18 : A18 N)
    (h19 : A19 N) (h22 : A22 N) :
    ∃ h, IsSCDE N N.Psi (capFeasible N) (devMNS N) h ∧
      IsSCDE N N.Psi (capFeasible N) (devLP N) h := by sorry

end SideConstrainedDTA.Existence
