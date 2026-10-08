-- Prove2me | Theorems.Thm_PrimalDualLDR_FixedRecourse_proposition_3
-- name    : PrimalDualLDR.FixedRecourse.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:03.015556+00:00
-- url     : https://prove2.me/theorems/0570113d-fe36-4dec-9ecb-d76d8a806a01
-- title:
--   Proposition 3 — $\emptyset\ne\operatorname{int}\mathcal K\subset\mathcal K_{\mathbb P}\subset\mathcal K$
-- statement:
--   Assume the standing assumptions of §2. Consider the two convex cones in $\mathbb R^k$
--   $$\mathcal K := \big\{z \in \mathbb R^k : (W - h e_1^\top) z \ge 0\big\},$$
--   $$\mathcal K_{\mathbb P} := \big\{z \in \mathbb R^k : \exists s \in \mathcal L^2_{k,1} \text{ with } \mathbb E(s(\xi)\xi) = z \text{ and } s(\xi) \ge 0\ \mathbb P\text{-a.s.}\big\}.$$
--   Then
--   $$\emptyset \ne \operatorname{int}\mathcal K \subseteq \mathcal K_{\mathbb P} \subseteq \mathcal K .$$
--
--   This is the dual counterpart of Proposition 1. $\mathcal K_{\mathbb P}$ is the set of first-order moment vectors of nonnegative square-integrable densities, a moment-feasibility condition that looks intractable; the proposition sandwiches it between the polyhedral cone $\mathcal K$ and its interior, which lets the last constraint of (2.6) be replaced by the finitely many linear constraints of (2.8).
--
--   **Formalization Note** $\operatorname{int}$ is the topological interior in $\mathbb R^k$ (product topology on `Fin k → ℝ`). The inclusions "$\subset$" are non-strict, as in the paper. $\mathcal L^2_{k,1}$ consists of Borel measurable square-integrable real-valued functions. **Repaired statement:** the formal statement adds the hypothesis $\widehat W \ne 0$ (some row $i \ge 3$ of $W$, 1-based, is nonzero), which the paper does not state. Without it the printed proposition is false: for $k = 1$, $l = 2$, $W = (1,-1)^\top$, $h = (1,-1)^\top$, $\mathbb P = \delta_1$, all standing assumptions hold, $W - he_1^\top = 0$, so $\mathcal K = \mathbb R$ while $\mathcal K_{\mathbb P} = [0,\infty)$. (The proof drops the constraint $e_1^\top z \ge 0$ as redundant, which fails exactly when $\widehat W = 0$.) Under the standing assumptions $\widehat W \ne 0$ holds automatically when $k \ge 2$, since $\Xi$ is bounded.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 7, Proposition 3

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.FixedRecourse

/-- Proposition 3 (p. 7): under the standing assumptions of §2, the cones
`𝒦 = {z : (W − h e_1ᵀ) z ≥ 0}` and `𝒦_P = {E(s(ξ)ξ) : s ∈ 𝓛²_{k,1}, s ≥ 0 P-a.s.}` satisfy
`∅ ≠ int 𝒦 ⊂ 𝒦_P ⊂ 𝒦`.

Repair (trap 30): the hypothesis `hW` says `Ŵ ≠ 0` (some row `i ≥ 2` of `W` is nonzero; rows
`0`, `1` are `±e_1ᵀ`). The page omits it, and the printed statement is false without it: for
`k = 1`, `l = 2`, `W = (1, −1)ᵀ`, `h = (1, −1)`, `P = δ_1`, the matrix `W − h e_1ᵀ` is `0`, so
`𝒦 = ℝ` while `𝒦_P = [0, ∞)`. Under the standing assumptions `Ŵ ≠ 0` is automatic when `k ≥ 2`. -/
theorem proposition_3 (σ : Setting) (hσ : σ.Standing)
    (hW : ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) :
    (interior σ.coneK).Nonempty ∧ interior σ.coneK ⊆ σ.coneKP ∧ σ.coneKP ⊆ σ.coneK := by sorry

end PrimalDualLDR.FixedRecourse
