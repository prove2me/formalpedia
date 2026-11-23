-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_Supplement_theorem_25
-- name    : ThinFlowSP.Breakpoints.Supplement.theorem_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:47:55.678931+00:00
-- url     : https://prove2.me/theorems/15f740dd-2ef7-482b-b77f-263dfb7f3fce
-- title:
--   Theorem 25, p. 17 — two right-monotone dynamic equilibria for a right-monotone inflow rate have the same earliest times function
-- statement:
--   Let $(G,\nu,\tau)$ be a network of the fluid queuing model and let the inflow rate $\nu_0$ (locally integrable, non-negative, zero almost everywhere on $\mathbb R_{<0}$) be right-monotone. Let $(f^+,f^-)$ and $(g^+,g^-)$ be dynamic equilibria for $\nu_0$ with earliest times functions $\ell$ and $\ell'$, and suppose both are right-monotone, i.e. every arc inflow rate $f^+_a$ and every $g^+_a$ is right-monotone (Definition 20). Then
--   $$\ell(\vartheta)=\ell'(\vartheta)\qquad\text{for all }\vartheta\in\mathbb R .$$
--
--   So within the class of right-monotone equilibria the earliest times, and with them the travel times of all particles, are determined by the inflow rate.
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
--   - reading: "two right-monotone dynamic equilibria" → dynamic equilibria (f⁺, f⁻), (g⁺, g⁻) for ν₀ in which every arc inflow rate f⁺_a, g⁺_a is right-monotone; reason: the first sentence of the proof (p. 17) fixes this reading: 'Let (f⁺, f⁻) be a dynamic equilibrium for inflow rate ν₀ such that f⁺_a is right-monotone for all a'
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 17, Theorem 25 and the first sentence of its proof; model pp. 3–4, Definition 1 p. 4, Definition 20 p. 15

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_FluidModel
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_DE
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_RightMonotone

open MeasureTheory

namespace ThinFlowSP.Breakpoints.Supplement

theorem theorem_25 (N : QNet) (hN : N.Standing) (ν0 : ℝ → ℝ) (hν0 : IsInflowRate ν0)
    (hrm : RightMonotone ν0) (fp fm gp gm : N.G.A → ℝ → ℝ) (ℓ ℓ' : ℝ → N.G.V → ℝ)
    (h₁ : IsDynEqWith N ν0 fp fm ℓ) (hr₁ : ∀ a, RightMonotone (fp a))
    (h₂ : IsDynEqWith N ν0 gp gm ℓ') (hr₂ : ∀ a, RightMonotone (gp a)) :
    ℓ = ℓ' := by sorry

end ThinFlowSP.Breakpoints.Supplement
