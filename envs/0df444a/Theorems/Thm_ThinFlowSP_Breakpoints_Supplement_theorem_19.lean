-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_Supplement_theorem_19
-- name    : ThinFlowSP.Breakpoints.Supplement.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:45:27.050032+00:00
-- url     : https://prove2.me/theorems/af2dcc54-8cbc-4d7a-982f-b336eccce583
-- title:
--   Theorem 19, p. 12 (corrected: ℓ real-valued) — earliest times functions of dynamic equilibria are the solutions of (DE)
-- statement:
--   Let $(G,\nu,\tau)$ be a network of the fluid queuing model (source $s\ne$ sink $t$, positive capacities, non-negative delays, no cycle of zero transit time, every vertex reachable from $s$) and $\nu_0$ an inflow rate (locally integrable, non-negative, zero almost everywhere on $\mathbb R_{<0}$). Let $\ell^0_v$ be the shortest distance from $s$ to $v$ with respect to $\tau$. For $\ell:\mathbb R\to\mathbb R^V$ and $\vartheta\in\mathbb R$ let $G'_\vartheta=(V,A'_\vartheta,A^*_\vartheta)$ with $A'_\vartheta=\{a=(v,w):\ell_w(\vartheta)\ge\ell_v(\vartheta)+\tau_a\}$ and $A^*_\vartheta=\{a=(v,w):\ell_w(\vartheta)>\ell_v(\vartheta)+\tau_a\}$, and let $\varrho^{G'}$ be the thin-flow label function, extended as on p. 12 to triples without $s$–$v$-paths.
--
--   Then $\ell$ is the earliest times function of a dynamic equilibrium (Definition 1) if and only if $\ell$ is locally absolutely continuous and solves
--   $$\ell(\vartheta)=\bigl(\vartheta+\ell^0_v\bigr)_{v\in V}\ \text{ for all }\vartheta\le0\qquad\text{and}\qquad\frac{d\ell}{d\vartheta}(\vartheta)=\varrho^{G'_\vartheta}\bigl(\nu_0(\vartheta)\bigr)\ \text{ for a.e. }\vartheta\ge0.\tag{DE}$$
--
--   The theorem turns the equilibrium problem into an initial value problem whose right-hand side is the thin-flow label function; Theorems 21, 24 and 25 are proved by solving it.
--
--   **Formalization Note** The network is a `QNet`: the base mission's multigraph `Net` (parallel arcs allowed) with capacities `ν` and delays `τ`; `QNet.Standing` collects the standing assumptions of p. 3 ($s\ne t$, positive capacities, non-negative delays, no cycle of zero transit time, every vertex reachable from `s`), and `IsInflowRate ν0` says that `ν0` is locally integrable, non-negative almost everywhere and zero almost everywhere on $\mathbb R_{<0}$. Locally absolutely continuous means absolutely continuous on every bounded interval (Mathlib's `AbsolutelyContinuousOnInterval`), and the derivative of $\ell$ is the derivative of the vector-valued map (`HasDerivAt`), which is the componentwise derivative. The labels are written $\ell$ in the paper and `ℓ` in Lean; $\nu_0$ is `ν0`.
--
--   Differences from the source:
--
--   - correction: ℓ: ℝ → ℝ^V_{≥0} in the statement → ℓ : ℝ → (V → ℝ); reason: ℓ_s(ϑ) = ϑ by (BE) (p. 4) and the initial condition ℓ(ϑ) = ϑ + ℓ⁰ on ϑ ≤ 0 make ℓ negative for ϑ < −ℓ⁰_v, so no function into ℝ^V_{≥0} is an earliest times function or a solution of (DE) and the printed Theorem 19 is vacuous; the proof of Theorem 19 (p. 13) itself uses lim_{ϑ→−∞} ℓ_v(ϑ) = −∞ and ℓ_v(ℝ) = ℝ. No case is excluded
--   - reading: s ∈ V is the source and t ∈ V the sink of a single commodity (p. 3) → s ≠ t is part of the standing assumptions; reason: the base mission reads §2 the same way (its Theorems 6, 13–15, 17, 18 assume s ≠ t); for s = t no static s–t-flow of positive value exists, so ϱ^{G′}(ν′₀) is undefined for ν′₀ > 0 (Theorem 13 fails) and (DE) has no solution, while the zero flow is an equilibrium
--   - encoding: ℓ_v(ϑ) is the minimum of ℓ_P(ϑ) over the s–v-paths P → the minimum over all directed s–v-walks; reason: every exit time map T_a is non-decreasing with T_a(ϑ) ≥ ϑ, so deleting a closed sub-walk never increases the arrival time; the minimum is the same
--   - encoding: z_a is the unique locally absolutely continuous solution of (QD), and z_a(ϑ) = F⁺_a(ϑ) − F⁻_a(ϑ + τ_a) is required → the function ϑ ↦ F⁺_a(ϑ) − F⁻_a(ϑ + τ_a) is required to be a locally absolutely continuous solution of (QD); reason: (QD) has exactly one such solution (p. 3), so the two requirements coincide
--   - encoding: q_a(ϑ) = min{q ≥ 0 : F⁻_a(ϑ + τ_a + q) ≥ F⁺_a(ϑ)} → the infimum of that set; reason: the set is closed and bounded below by 0, and for a feasible flow it is nonempty (q_a = z_a/ν_a, p. 4), so the infimum is the minimum
--   - encoding: rates are classes of L¹_loc functions identified almost everywhere; f± take values in ℝ^A_{≥0} → rates are functions ℝ → ℝ; f⁺_a, f⁻_a are non-negative everywhere, ν₀ almost everywhere, and every condition on them is an almost-everywhere condition or an integral; reason: the integral and a.e. conditions depend only on the rate classes; pointwise non-negativity selects non-negative representatives, which every non-negative a.e. class admits
--   - encoding: dℓ/dϑ(ϑ) = ϱ^{G′_ϑ}(ν₀(ϑ)), with ϱ^{G′} the label function of p. 11 extended on p. 12 → ℓ is differentiable at ϑ and its derivative is the label vector, with label 1 at s, of some normalized thin s–t-flow with resetting of value ν₀(ϑ) in (V, A′_ϑ, A*_ϑ) when that triple is a shortest path graph with resetting, and the 0/1 vector of p. 12 otherwise; reason: by Theorem 13 and Corollary 15 that label vector exists and is unique for ν₀(ϑ) ≥ 0, which holds almost everywhere; this is the definition of ϱ^{G′} on p. 11. A′_ϑ is always acyclic because there is no cycle of zero transit time, so 'not a shortest path graph' is the p. 12 case
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 12, Theorem 19 and (DE); model pp. 3–4; ϱ^{G′} p. 11 and its extension p. 12

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_FluidModel
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_DE
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_RightMonotone

open MeasureTheory

namespace ThinFlowSP.Breakpoints.Supplement

theorem theorem_19 (N : QNet) (hN : N.Standing) (ν0 : ℝ → ℝ) (hν0 : IsInflowRate ν0)
    (ℓ : ℝ → N.G.V → ℝ) :
    (∃ fp fm : N.G.A → ℝ → ℝ, IsDynEqWith N ν0 fp fm ℓ) ↔ SolvesDE N ν0 ℓ := by sorry

end ThinFlowSP.Breakpoints.Supplement
