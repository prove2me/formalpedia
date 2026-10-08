-- Prove2me | Theorems.Thm_PrimalDualLDR_FixedRecourse_theorem_1
-- name    : PrimalDualLDR.FixedRecourse.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:18.16007+00:00
-- url     : https://prove2.me/theorems/e9b4c975-1a71-486b-811a-5aee339272a5
-- title:
--   Theorem 1 — with fixed recourse and strict feasibility, $\mathcal{SP}^u$ and $\mathcal{SP}^l$ equal the LPs (2.3) and (2.8)
-- statement:
--   Consider the one-stage stochastic program with fixed recourse
--   $$\mathcal{SP}:\qquad \min_{x\in\mathcal L^2_{k,n}} \mathbb E\big(c(\xi)^\top x(\xi)\big)\quad\text{s.t.}\quad Ax(\xi)\le b(\xi)\ \ \mathbb P\text{-a.s.},$$
--   with $c(\xi) = C\xi$, $b(\xi) = B\xi$, and assume that $\mathbb P$ has a polyhedral support $\Xi = \{\xi : W\xi \ge h\}$ of the type (2.1): nonempty, bounded, with $W, h$ of the form (2.1b), spanning $\mathbb R^k$. Assume further that $\mathcal{SP}$ is strictly feasible (2.9). Let $M = \mathbb E(\xi\xi^\top)$. Then
--
--   1. the primal linear-decision-rule problem $\mathcal{SP}^u$ ($\min \operatorname{Tr}(MC^\top X)$ s.t. $AX\xi+S\xi=B\xi$, $S\xi\ge0$ $\mathbb P$-a.s.) has the same optimal value as the linear program (2.3),
--   $$\min_{X,\Lambda}\ \operatorname{Tr}(MC^\top X)\ \ \text{s.t.}\ \ AX+\Lambda W=B,\ \Lambda h\ge0,\ \Lambda\ge0;$$
--   2. the dual linear-decision-rule problem $\mathcal{SP}^l$ ($\min \mathbb E(c(\xi)^\top x(\xi))$ over $x\in\mathcal L^2_{k,n}$, $s\in\mathcal L^2_{k,m}$ s.t. $\mathbb E([Ax(\xi)+s(\xi)-b(\xi)]\xi^\top)=0$, $s(\xi)\ge0$ $\mathbb P$-a.s.) has the same optimal value as the linear program (2.8),
--   $$\min_{X,S}\ \operatorname{Tr}(MC^\top X)\ \ \text{s.t.}\ \ AX+S=B,\ \ (W-he_1^\top)MS^\top\ge0.$$
--
--   The formal statement adds one hypothesis the paper does not state: $\widehat W \ne 0$, i.e. some row of $W$ below the first two is nonzero (see the Formalization Note).
--
--   Since $\mathcal{SP}^u$ is an upper and $\mathcal{SP}^l$ a lower bound on $\mathcal{SP}$, the theorem brackets the optimal value of the (generally #P-hard) stochastic program between two explicit linear programs whose size is polynomial in $k, l, m, n$.
--
--   **Formalization Note** "Equivalent" is formalized as equality of optimal values, each the infimum of the objective over the feasible set in $[-\infty,+\infty]$ ($+\infty$ if infeasible, $-\infty$ if unbounded). Strict feasibility is a hypothesis of both equalities, as printed, although the first holds without it. The paper's last sentence (the LP sizes are polynomial, so they are efficiently solvable) is informal and is not part of the statement. **Repaired statement:** the hypothesis $\widehat W \ne 0$ is added because the printed theorem is false without it: for $k = 1$, $l = 2$, $W = (1,-1)^\top$, $h = (1,-1)^\top$, $\mathbb P = \delta_1$, $n = m = 1$, $A = B = 1$, $C = -1$, every assumption of the theorem holds, $\mathcal{SP}^l$ has value $-1$, but $W - he_1^\top = 0$, so (2.8) has no sign constraint on $S$ and value $-\infty$. The paper's proof of Proposition 3 drops the constraint $e_1^\top z \ge 0$ as redundant, which fails exactly when $\widehat W = 0$. Under the standing assumptions $\widehat W \ne 0$ holds automatically when $k \ge 2$ (a bounded $\Xi$ forces it), so the repair only excludes this degenerate one-point case.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 10, Theorem 1

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.FixedRecourse

/-- Theorem 1 (p. 10): if `P` has a polyhedral support of the type (2.1) while `SP` has fixed recourse
and is strictly feasible, then `SP^u` and `SP^l` are equivalent to the linear programs (2.3) and
(2.8), respectively: their optimal values coincide.

Repair (trap 30): the hypothesis `hW` says `Ŵ ≠ 0` (some row `i ≥ 2` of `W` is nonzero; rows
`0`, `1` are `±e_1ᵀ`). The page omits it, and the printed statement is false without it: for
`k = 1`, `l = 2`, `W = (1, −1)ᵀ`, `h = (1, −1)`, `P = δ_1`, the matrix `W − h e_1ᵀ` is `0`, so
`𝒦 = ℝ` while `𝒦_P = [0, ∞)`; with `n = m = 1`, `A = B = 1`, `C = −1` (strictly feasible with
`x̄ = 0`, `s̄(ξ) = ξ`) the program (2.8) loses `S ≥ 0` and has value `−∞`, while (2.6) and `SP^l`
have value `−1`. Under the standing assumptions `Ŵ ≠ 0` is automatic when `k ≥ 2`. -/
theorem theorem_1 (σ : Setting) (hσ : σ.Standing)
    (hW : ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) (hsf : σ.StrictlyFeasible) :
    σ.valSPu = σ.valLP23 ∧ σ.valSPl = σ.valLP28 := by sorry

end PrimalDualLDR.FixedRecourse
