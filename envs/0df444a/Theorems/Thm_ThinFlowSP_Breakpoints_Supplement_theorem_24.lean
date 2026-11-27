-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_Supplement_theorem_24
-- name    : ThinFlowSP.Breakpoints.Supplement.theorem_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T11:47:30.183068+00:00
-- url     : https://prove2.me/theorems/8d28f1db-a661-484d-9fa3-1807bf06e382
-- title:
--   Theorem 24, p. 16 — dynamic equilibria exist for every non-negative, right-monotone, locally integrable inflow rate
-- statement:
--   Let $(G,\nu,\tau)$ be a network of the fluid queuing model (source $s\ne$ sink $t$, positive capacities, non-negative delays, no cycle of zero transit time, every vertex reachable from $s$), and let $\nu_0:\mathbb R\to\mathbb R$ be an inflow rate that is
--   1. non-negative (almost everywhere) and zero almost everywhere on $\mathbb R_{<0}$,
--   2. right-monotone (Definition 20),
--   3. locally integrable.
--
--   Then there exists a dynamic equilibrium (Definition 1) for $\nu_0$:
--   $$\exists\,(f^+,f^-)\ \text{feasible, with earliest times function }\ell,\ \text{such that } f^+_a=0 \text{ a.e. on } \{\ell_v(\vartheta): a=(v,w)\text{ inactive relative to }\vartheta\}\ \text{for every arc } a.$$
--
--   This extends the existence of dynamic equilibria from piecewise constant to right-monotone inflow rates.
--
--   **Formalization Note** The network is a `QNet`: the base mission's multigraph `Net` (parallel arcs allowed) with capacities `ν` and delays `τ`; `QNet.Standing` collects the standing assumptions of p. 3 ($s\ne t$, positive capacities, non-negative delays, no cycle of zero transit time, every vertex reachable from `s`), and `IsInflowRate ν0` says that `ν0` is locally integrable, non-negative almost everywhere and zero almost everywhere on $\mathbb R_{<0}$. Locally absolutely continuous means absolutely continuous on every bounded interval (Mathlib's `AbsolutelyContinuousOnInterval`), and the derivative of $\ell$ is the derivative of the vector-valued map (`HasDerivAt`), which is the componentwise derivative. The labels are written $\ell$ in the paper and `ℓ` in Lean; $\nu_0$ is `ν0`.
--
--   Differences from the source:
--
--   - reading: s ∈ V is the source and t ∈ V the sink of a single commodity (p. 3) → s ≠ t is part of the standing assumptions; reason: the base mission reads §2 the same way (its Theorems 6, 13–15, 17, 18 assume s ≠ t); for s = t no static s–t-flow of positive value exists, so ϱ^{G′}(ν′₀) is undefined for ν′₀ > 0 (Theorem 13 fails) and (DE) has no solution, while the zero flow is an equilibrium
--   - encoding: ℓ_v(ϑ) is the minimum of ℓ_P(ϑ) over the s–v-paths P → the minimum over all directed s–v-walks; reason: every exit time map T_a is non-decreasing with T_a(ϑ) ≥ ϑ, so deleting a closed sub-walk never increases the arrival time; the minimum is the same
--   - encoding: z_a is the unique locally absolutely continuous solution of (QD), and z_a(ϑ) = F⁺_a(ϑ) − F⁻_a(ϑ + τ_a) is required → the function ϑ ↦ F⁺_a(ϑ) − F⁻_a(ϑ + τ_a) is required to be a locally absolutely continuous solution of (QD); reason: (QD) has exactly one such solution (p. 3), so the two requirements coincide
--   - encoding: q_a(ϑ) = min{q ≥ 0 : F⁻_a(ϑ + τ_a + q) ≥ F⁺_a(ϑ)} → the infimum of that set; reason: the set is closed and bounded below by 0, and for a feasible flow it is nonempty (q_a = z_a/ν_a, p. 4), so the infimum is the minimum
--   - encoding: rates are classes of L¹_loc functions identified almost everywhere; f± take values in ℝ^A_{≥0} → rates are functions ℝ → ℝ; f⁺_a, f⁻_a are non-negative everywhere, ν₀ almost everywhere, and every condition on them is an almost-everywhere condition or an integral; reason: the integral and a.e. conditions depend only on the rate classes; pointwise non-negativity selects non-negative representatives, which every non-negative a.e. class admits
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 16, Theorem 24; model pp. 3–4, Definition 1 p. 4, Definition 20 p. 15

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_FluidModel
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_DE
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_RightMonotone

open MeasureTheory

namespace ThinFlowSP.Breakpoints.Supplement

theorem theorem_24 (N : QNet) (hN : N.Standing) (ν0 : ℝ → ℝ) (hν0 : IsInflowRate ν0)
    (hrm : RightMonotone ν0) :
    ∃ fp fm : N.G.A → ℝ → ℝ, IsDynEq N ν0 fp fm := by sorry

end ThinFlowSP.Breakpoints.Supplement
