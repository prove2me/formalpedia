-- Prove2me | Theorems.Thm_PrimalDualLDR_RandomRecourse_theorem_2_primal
-- name    : PrimalDualLDR.RandomRecourse.theorem_2_primal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:43:59.981454+00:00
-- url     : https://prove2.me/theorems/ca4ae36c-1a55-40ec-aae0-b25a4bc1d22f
-- title:
--   Theorem 2 (primal half) — the SDP (3.14) conservatively approximates 𝒮𝒫^u, and val 𝒮𝒫^u = val (3.14) for l = 1
-- statement:
--   Let $\mathbb P$ be a probability measure on $\mathbb R^k$ whose support is the quadratically constrained set
--   $$
--   \Xi=\big\{\xi\in\mathbb R^k:\ e_1^\top\xi=1,\ \xi^\top W_\ell\xi\ge0,\ \ell=1,\dots,l\big\}\qquad(3.11)
--   $$
--   with symmetric $W_1,\dots,W_l$, and assume $\Xi$ is nonempty, bounded and spans $\mathbb R^k$. Consider the one-stage stochastic program $\mathcal{SP}$ with costs $c(\xi)=C\xi$, right-hand side $b(\xi)=B\xi$ and random recourse matrix $A(\xi)$ with rows $\xi^\top A_\mu$; its primal linear decision rule approximation $\mathcal{SP}^u$ (decisions $X\xi$, slacks $\xi^\top S_\mu\xi$); and the SDP (3.14), both with objective $\operatorname{Tr}(MC^\top X)$, $M=\mathbb E(\xi\xi^\top)$. Then:
--
--   1. **(3.14) conservatively approximates $\mathcal{SP}^u$.** Every $(X,S,\Lambda)$ feasible in (3.14) yields $(X,S)$ feasible in $\mathcal{SP}^u$ with the same objective value; hence
--   $$
--   \operatorname{val}\mathcal{SP}^u\le\operatorname{val}(3.14).
--   $$
--   2. **Exactness for one quadratic constraint.** If $l=1$ and $\mathcal{SP}$ is strictly feasible, then $\mathcal{SP}^u$ is equivalent to (3.14):
--   $$
--   \operatorname{val}\mathcal{SP}^u=\operatorname{val}(3.14).
--   $$
--
--   The result turns the semi-infinite program $\mathcal{SP}^u$, an upper bound on the stochastic program $\mathcal{SP}$, into a semidefinite program of size polynomial in $k,l,m,n$, whose value is an upper bound on $\mathcal{SP}^u$ in general and equal to it when the support is cut out by a single quadratic inequality (an ellipsoid in the hyperplane $e_1^\top\xi=1$).
--
--   **Formalization Note** This is the primal half of the paper's Theorem 2. The clauses "the SDP (3.18) progressively approximates $\mathcal{SP}^l$" and, for $l=1$, "$\mathcal{SP}^l$ is equivalent to (3.18)" are false in this preprint (a strictly feasible instance with $l=1$ has $\operatorname{val}(3.18)\approx1.170>\ln3=\operatorname{val}\mathcal{SP}\ge\operatorname{val}\mathcal{SP}^l$) and are not stated; the claim that the SDP sizes are polynomial and efficiently solvable is informal and omitted. Optimal values are `EReal` infima ($+\infty$ if infeasible, $-\infty$ if unbounded). "Equivalent" is read as equality of optimal values. Strict feasibility of $\mathcal{SP}$ is condition (2.9) of §2 with $A$ replaced by $A(\xi)$; it is kept in clause 2 as printed.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 17, Theorem 2 (clauses on (3.14) and SP^u)

import Mathlib
import Definitions.Def_PrimalDualLDR_RandomRecourse_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.RandomRecourse

/-- **Kuhn, Wiesemann, Georghiou (preprint 2009), Theorem 2, p. 17 — primal half.** If `P` has a
quadratically constrained support `Ξ` of the type (3.11) (nonempty, bounded, spanning `ℝ^k`), then
(a) the SDP (3.14) conservatively approximates `𝒮𝒫^u`: every `(X, S, Λ)` feasible in (3.14)
gives `(X, S)` feasible in `𝒮𝒫^u` with the same objective `Tr(MCᵀX)`, hence
`val 𝒮𝒫^u ≤ val (3.14)`; and
(b) if `l = 1` and `𝒮𝒫` is strictly feasible, then `𝒮𝒫^u` is equivalent to (3.14):
`val 𝒮𝒫^u = val (3.14)`.

The clauses of Theorem 2 about the SDP (3.18) and `𝒮𝒫^l` are not stated (false in this
preprint); "polynomial size / efficiently solvable" is informal and omitted. -/
theorem theorem_2_primal (σ : Setting) (hσ : σ.Standing) :
    (∀ (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (S : Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ)
        (Λ : Matrix (Fin σ.m) (Fin σ.l) ℝ), σ.Feas314 X S Λ → σ.FeasSPu X S) ∧
      σ.valSPu ≤ σ.valSDP314 ∧
      (σ.l = 1 → σ.StrictlyFeasible → σ.valSPu = σ.valSDP314) := by sorry

end PrimalDualLDR.RandomRecourse
