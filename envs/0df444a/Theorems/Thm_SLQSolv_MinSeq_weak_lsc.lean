-- Prove2me | Theorems.Thm_SLQSolv_MinSeq_weak_lsc
-- name    : SLQSolv.MinSeq.weak_lsc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:55.593397+00:00
-- url     : https://prove2.me/theorems/6ffdd166-d20b-43ba-b70c-08c9a186ff73
-- title:
--   §6, proof of Theorem 6.2, p. 2302 — u ↦ J(t, x; u) is sequentially weakly lower semicontinuous on 𝒰[t, T]
-- statement:
--   Assume (H1)–(H2) and that $u\mapsto J^0(0,0;u)$ is convex. Let $(t,x)\in[0,T)\times\mathbb R^n$, let $u_k,u\in\mathcal U[t,T]$, and suppose $u_k\to u$ weakly in $\mathcal U[t,T]$. Then
--
--   $$
--   J(t,x;u)\le\liminf_{k\to\infty}J(t,x;u_k).
--   $$
--
--   The paper records this as a consequence of $u\mapsto J(t,x;u)$ being convex and continuous; it is the step that turns a weak limit of the minimizing sequence into an optimal control.
--
--   **Formalization Note** The liminf is taken in the extended reals, so the statement is meaningful when $J(t,x;u_k)$ is unbounded. Weak convergence is tested against every $v\in\mathcal U[t,T]$. (H1)–(H2) are the standing assumptions; the state, cost, value function and optimality notions are those of the shared `Setting` module.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §6, proof of Theorem 6.2, p. 2302 ("Since u(·) ↦ J(t, x; u(·)) is convex and continuous, it is hence sequentially weakly lower semicontinuous.")

import Mathlib
import Definitions.Def_SLQSolv_MinSeq_Sequence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix

namespace SLQSolv.MinSeq

/-- §6, proof of Theorem 6.2, p. 2302: under convexity of `u ↦ J⁰(0, 0; u)`, the map
`u ↦ J(t, x; u)` is sequentially weakly lower semicontinuous on `𝒰[t, T]`:
`uₖ → u` weakly implies `J(t, x; u) ≤ liminf J(t, x; uₖ)` (in `EReal`). -/
theorem weak_lsc {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d)
    (hconv : IsConvexJ0 Bs d) (t : ℝ≥0) (ht : t < d.T) (x : Fin n → ℝ)
    (uk : ℕ → ℝ≥0 → Ω → Fin m → ℝ) (huk : ∀ k, Adm Bs d t (uk k))
    (u : ℝ≥0 → Ω → Fin m → ℝ) (hu : Adm Bs d t u) (hw : WeakConvU Bs d t uk u) :
    ((J Bs d t x u : ℝ) : EReal) ≤
      Filter.liminf (fun k => ((J Bs d t x (uk k) : ℝ) : EReal)) atTop := by sorry

end SLQSolv.MinSeq
