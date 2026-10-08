-- Prove2me | Theorems.Thm_PrimalDualLDR_FixedRecourse_proposition_4
-- name    : PrimalDualLDR.FixedRecourse.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:46.008688+00:00
-- url     : https://prove2.me/theorems/15941721-3034-42f1-9d13-1c46a92d94f6
-- title:
--   Proposition 4 — if $\mathcal{SP}$ is strictly feasible (2.9), (2.6) and (2.8) have the same optimal value
-- statement:
--   Assume the standing assumptions of §2, and suppose that $\mathcal{SP}$ is strictly feasible: there are $\varepsilon > 0$ and decision rules $\bar x \in \mathcal L^2_{k,n}$, $\bar s \in \mathcal L^2_{k,m}$ with
--   $$A\bar x(\xi) + \bar s(\xi) = b(\xi)\quad\text{and}\quad \bar s(\xi) \ge \varepsilon e\qquad\mathbb P\text{-a.s.},\tag{2.9}$$
--   where $e \in \mathbb R^m$ is the all-ones vector. Then the optimal values of problem (2.6) and of the linear program (2.8),
--   $$\min_{X,S}\ \operatorname{Tr}(MC^\top X)\ \ \text{s.t.}\ \ AX+S=B,\ \ (W-he_1^\top)MS^\top\ge0,$$
--   coincide (as elements of $[-\infty,+\infty]$).
--
--   Without strict feasibility the two values only bracket each other through Proposition 3; strict feasibility removes the gap, and with the §2.4 reformulation this identifies the dual approximation $\mathcal{SP}^l$ with a linear program.
--
--   **Formalization Note** **Repaired statement:** the formal statement adds the hypothesis $\widehat W \ne 0$ (some row $i \ge 3$ of $W$, 1-based, is nonzero), which the paper does not state. Without it the printed proposition is false: for $k = 1$, $l = 2$, $W = (1,-1)^\top$, $h = (1,-1)^\top$, $\mathbb P = \delta_1$, $n = m = 1$, $A = B = 1$, $C = -1$, problem $\mathcal{SP}$ is strictly feasible ($\bar x = 0$, $\bar s(\xi) = \xi$), $W - he_1^\top = 0$ so (2.8) has no sign constraint on $S$ and value $-\infty$, while (2.6) forces $S \ge 0$ and has value $-1$. Under the standing assumptions $\widehat W \ne 0$ holds automatically when $k \ge 2$. Optimal values are infima in $[-\infty, +\infty]$.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 9, Proposition 4, (2.9)

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.FixedRecourse

/-- Proposition 4 (p. 9): under the standing assumptions of §2, if `SP` is strictly feasible (2.9),
then the optimal values of (2.6) and (2.8) coincide.

Repair (trap 30): the hypothesis `hW` says `Ŵ ≠ 0` (some row `i ≥ 2` of `W` is nonzero; rows
`0`, `1` are `±e_1ᵀ`). The page omits it, and the printed statement is false without it: for
`k = 1`, `l = 2`, `W = (1, −1)ᵀ`, `h = (1, −1)`, `P = δ_1`, the matrix `W − h e_1ᵀ` is `0`, so
`𝒦 = ℝ` while `𝒦_P = [0, ∞)`; with `n = m = 1`, `A = B = 1`, `C = −1` (strictly feasible with
`x̄ = 0`, `s̄(ξ) = ξ`) the program (2.8) loses `S ≥ 0` and has value `−∞`, while (2.6) and `SP^l`
have value `−1`. Under the standing assumptions `Ŵ ≠ 0` is automatic when `k ≥ 2`. -/
theorem proposition_4 (σ : Setting) (hσ : σ.Standing)
    (hW : ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) (hsf : σ.StrictlyFeasible) :
    σ.valLP26 = σ.valLP28 := by sorry

end PrimalDualLDR.FixedRecourse
