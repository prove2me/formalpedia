-- Prove2me | Theorems.Thm_SideConstrainedDTA_Existence_proposition_7_3_mns_lp
-- name    : SideConstrainedDTA.Existence.proposition_7_3_mns_lp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:26.479993+00:00
-- url     : https://prove2.me/theorems/c283bd07-dac2-4789-9c89-7b3f0f6314e3
-- title:
--   Proposition 7.3 (inclusion strong MNSDE ⊆ strong LPDE), p. 36, as used on p. 40
-- statement:
--   Let $S$ be the set (23) of capacity-feasible walk inflows in $\Lambda(Q)$. For any effective walk delay operator $\Phi$: if $h^*$ is a **strong dynamic Marcotte–Nguyen–Schoeb equilibrium** (an SCDE w.r.t. $S$ and the admissible $\gamma$-deviations (26)), then $h^*$ is a **strong dynamic Larsson–Patriksson equilibrium** (an SCDE w.r.t. $S$ and the admissible $\gamma$-deviations (24)):
--   $$\text{strong MNSDE}\subseteq\text{strong LPDE}.$$
--
--   This inclusion is part of Proposition 7.3; the proof of Theorem 7.6 uses it to reduce existence of a strong LPDE to existence of a strong MNSDE.
--
--   **Formalization Note.** Only this inclusion of Proposition 7.3 is posed; the other inclusions, properness and independence statements are not. Both deviation sets include the condition $H_{p\to q}(h,\gamma,\Delta)\in\Lambda(Q)$ that §7 adds implicitly. Node indices of arrival times are 0-based (`tau h q j t` is the paper's $\tau^{j+1}_q(h,t)$).
-- source:
--   Graf, Harks, Side-Constrained Dynamic Traffic Equilibria, arXiv:2211.03194v3, p. 36, Proposition 7.3 (first diagram, left vertical inclusion), applied on p. 40 (proof of Theorem 7.6)

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

open MeasureTheory Set Filter Topology

namespace SideConstrainedDTA.Existence

/-- Proposition 7.3 (inclusion strong MNSDE ⊆ strong LPDE), p. 36: for any delay operator `Φ`,
every strong MNSDE (SCDE w.r.t. (23) and (26)) is a strong LPDE (SCDE w.r.t. (23) and (24)). -/
theorem proposition_7_3_mns_lp {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I]
    [DecidableEq W] (N : Model I W E) (hN : N.Standing) (Φ : (W → ℝ → ℝ) → W → ℝ → ℝ)
    (h : W → ℝ → ℝ) :
    IsSCDE N Φ (capFeasible N) (devMNS N) h → IsSCDE N Φ (capFeasible N) (devLP N) h := by sorry

end SideConstrainedDTA.Existence
