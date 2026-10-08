-- Prove2me | Theorems.Thm_SingleMachinePrec_IntervalReduction_claim_2
-- name    : SingleMachinePrec.IntervalReduction.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:31:44.048177+00:00
-- url     : https://prove2.me/theorems/0cf1bb85-7f36-42a7-b71b-1a500ace289e
-- title:
--   Claim 2 — an incomparable pair has weight 1 if it lies in $D$, and at most $1/k$ otherwise
-- statement:
--   Let $S$ be the Stage 2 instance with parameter $k>1$, with precedence constraints the interval order $I$, and let $D$ be the set of pairs defined on p. 663. For every pair $(i,j)$ of incomparable jobs,
--   $$p_i w_j = 1 \text{ if } (i,j)\in D, \qquad p_i w_j\le \frac1k \text{ if } (i,j)\notin D.$$
--
--   So the nodes of $G^S_I$ of weight one are exactly the pairs of $D$, and every other node has weight at most $1/k$.
--
--   **Formalization Note** The statement holds for any $k>1$; the proof later takes $k=n^2+1$.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 663, Claim 2

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

/-- Claim 2 (p. 663): an incomparable pair of jobs `(i, j)` has `p_i w_j = 1` if `(i, j) ∈ D`,
and `p_i w_j ≤ 1/k` otherwise. -/
theorem claim_2 {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) (k : ℝ) (hk : 1 < k)
    (x y : Job L) (hxy : Incomparable (prec L) x y) :
    (InD L x y → procTime L k x * weight L k y = 1) ∧
    (¬ InD L x y → procTime L k x * weight L k y ≤ 1 / k) := by sorry

end SingleMachinePrec.IntervalReduction
