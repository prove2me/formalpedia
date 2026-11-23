-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_Supplement_theorem_21
-- name    : ThinFlowSP.Breakpoints.Supplement.theorem_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:46:56.042794+00:00
-- url     : https://prove2.me/theorems/8c83fa62-d6f0-4da4-b65d-b151e044109d
-- title:
--   Theorem 21, p. 15 (corrected: ℓ real-valued) — α-extension: a solution of (DE) on (−∞, ϑ] extends to (−∞, ϑ + α]
-- statement:
--   Let $(G,\nu,\tau)$ be a network of the fluid queuing model and let the inflow rate $\nu_0$ (locally integrable, non-negative, zero almost everywhere on $\mathbb R_{<0}$) be right-monotone. Let $\vartheta\ge0$ and let $\ell$ fulfil the differential equation (DE) on $(-\infty,\vartheta]$: its components are absolutely continuous on every bounded interval inside $(-\infty,\vartheta]$,
--   $$\ell(\theta)=(\theta+\ell^0_v)_{v\in V}\ \text{for }\theta\le0,\qquad \frac{d\ell}{d\theta}(\theta)=\varrho^{G'_\theta}\bigl(\nu_0(\theta)\bigr)\ \text{for a.e. }\theta\in[0,\vartheta].$$
--   Then there is $\alpha>0$ such that $\ell$ can be extended to fulfil (DE) on $(-\infty,\vartheta+\alpha]$: there is $\hat\ell$ with $\hat\ell=\ell$ on $(-\infty,\vartheta]$ that fulfils (DE) on $(-\infty,\vartheta+\alpha]$.
--
--   Iterating this extension, one phase at a time, is the constructive method for dynamic equilibria; together with Zorn's lemma it gives Theorem 24.
--
--   **Formalization Note** The network is a `QNet`: the base mission's multigraph `Net` (parallel arcs allowed) with capacities `ν` and delays `τ`; `QNet.Standing` collects the standing assumptions of p. 3 ($s\ne t$, positive capacities, non-negative delays, no cycle of zero transit time, every vertex reachable from `s`), and `IsInflowRate ν0` says that `ν0` is locally integrable, non-negative almost everywhere and zero almost everywhere on $\mathbb R_{<0}$. Locally absolutely continuous means absolutely continuous on every bounded interval (Mathlib's `AbsolutelyContinuousOnInterval`), and the derivative of $\ell$ is the derivative of the vector-valued map (`HasDerivAt`), which is the componentwise derivative. The labels are written $\ell$ in the paper and `ℓ` in Lean; $\nu_0$ is `ν0`. The function $\ell$ is a function on $\mathbb R$, and the hypothesis constrains only its values on $(-\infty,\vartheta]$.
--
--   Differences from the source:
--
--   - correction: ℓ: ℝ → ℝ^V_{≥0} on (−∞, ϑ] in the statement → ℓ : ℝ → (V → ℝ); reason: ℓ_s(ϑ) = ϑ by (BE) (p. 4) and the initial condition ℓ(ϑ) = ϑ + ℓ⁰ on ϑ ≤ 0 make ℓ negative for ϑ < −ℓ⁰_v, so no function into ℝ^V_{≥0} is an earliest times function or a solution of (DE) and the printed Theorem 21 is vacuous; the proof of Theorem 19 (p. 13) itself uses lim_{ϑ→−∞} ℓ_v(ϑ) = −∞ and ℓ_v(ℝ) = ℝ. No case is excluded
--   - reading: s ∈ V is the source and t ∈ V the sink of a single commodity (p. 3) → s ≠ t is part of the standing assumptions; reason: the base mission reads §2 the same way (its Theorems 6, 13–15, 17, 18 assume s ≠ t); for s = t no static s–t-flow of positive value exists, so ϱ^{G′}(ν′₀) is undefined for ν′₀ > 0 (Theorem 13 fails) and (DE) has no solution, while the zero flow is an equilibrium
--   - encoding: ℓ: (−∞, ϑ] → ℝ^V fulfils (DE) on (−∞, ϑ], and ℓ is extended to (−∞, ϑ + α] → ℓ : ℝ → (V → ℝ) with only its values on (−∞, ϑ] constrained (derivative condition for a.e. θ ∈ [0, ϑ)); the extension is some ℓ' equal to ℓ on (−∞, ϑ] that fulfils the same condition up to ϑ + α; reason: a derivative at θ < ϑ only involves values near θ, and the point ϑ is a null set; this is exactly a function on the half-line and its extension
--   - encoding: dℓ/dϑ(ϑ) = ϱ^{G′_ϑ}(ν₀(ϑ)), with ϱ^{G′} the label function of p. 11 extended on p. 12 → ℓ is differentiable at ϑ and its derivative is the label vector, with label 1 at s, of some normalized thin s–t-flow with resetting of value ν₀(ϑ) in (V, A′_ϑ, A*_ϑ) when that triple is a shortest path graph with resetting, and the 0/1 vector of p. 12 otherwise; reason: by Theorem 13 and Corollary 15 that label vector exists and is unique for ν₀(ϑ) ≥ 0, which holds almost everywhere; this is the definition of ϱ^{G′} on p. 11. A′_ϑ is always acyclic because there is no cycle of zero transit time, so 'not a shortest path graph' is the p. 12 case
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 15, Theorem 21; (DE) p. 12; Definition 20 p. 15

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Network
import Definitions.Def_ThinFlowSP_Breakpoints_Model
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_FluidModel
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_DE
import Definitions.Def_ThinFlowSP_Breakpoints_Supplement_RightMonotone

open MeasureTheory

namespace ThinFlowSP.Breakpoints.Supplement

theorem theorem_21 (N : QNet) (hN : N.Standing) (ν0 : ℝ → ℝ) (hν0 : IsInflowRate ν0)
    (hrm : RightMonotone ν0) (ϑ : ℝ) (hϑ : 0 ≤ ϑ) (ℓ : ℝ → N.G.V → ℝ)
    (hℓ : SolvesDEUpTo N ν0 ϑ ℓ) :
    ∃ α > 0, ∃ ℓ' : ℝ → N.G.V → ℝ,
      (∀ θ ≤ ϑ, ℓ' θ = ℓ θ) ∧ SolvesDEUpTo N ν0 (ϑ + α) ℓ' := by sorry

end ThinFlowSP.Breakpoints.Supplement
