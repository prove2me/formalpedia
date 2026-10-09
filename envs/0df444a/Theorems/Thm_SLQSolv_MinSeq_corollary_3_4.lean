-- Prove2me | Theorems.Thm_SLQSolv_MinSeq_corollary_3_4
-- name    : SLQSolv.MinSeq.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:53.326982+00:00
-- url     : https://prove2.me/theorems/e11d3f35-3545-41e8-b350-decf686b0d1d
-- title:
--   Corollary 3.4 (i)–(v), p. 2283 — convexity of u ↦ J(t, x; u) or J⁰(t, x; u) for some x, for all x, and J⁰(t, 0; ·) ⩾ 0 are equivalent
-- statement:
--   Assume (H1)–(H2) and fix $t\in[0,T)$. Write $J^0$ for the cost of Problem (SLQ)$^0$, where $b,\sigma,g,q,\rho=0$. The following are equivalent:
--
--   1. $u\mapsto J(t,x;u)$ is convex on $\mathcal U[t,T]$ for some $x\in\mathbb R^n$;
--   2. $u\mapsto J(t,x;u)$ is convex for every $x\in\mathbb R^n$;
--   3. $u\mapsto J^0(t,x;u)$ is convex for some $x$;
--   4. $u\mapsto J^0(t,x;u)$ is convex for every $x$;
--   5. $$J^0(t,0;u)\ge0\qquad\text{for all }u\in\mathcal U[t,T].$$
--
--   Convexity of the cost thus does not depend on the initial state or on the inhomogeneous terms, and is the positivity condition (5.6) at time $t$. Section 6 uses it to pass from the hypothesis of Theorem 6.2, convexity of $J^0(0,0;\cdot)$, to convexity of $J(t,x;\cdot)$.
--
--   **Formalization Note** The paper's item (vi), $M_2(t)\ge0$, is not stated: the operator $M_2(t)$ comes from Proposition 3.1, which the paper quotes from [30] without proof, and no definition of it is part of this mission. Convexity is the inequality $J(\theta u+(1-\theta)v)\le\theta J(u)+(1-\theta)J(v)$ over admissible $u,v$ and $\theta\in[0,1]$. (H1)–(H2) are the standing assumptions; the state, cost, value function and optimality notions are those of the shared `Setting` module.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Corollary 3.4, p. 2283

import Mathlib
import Definitions.Def_SLQSolv_MinSeq_Sequence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix

namespace SLQSolv.MinSeq

/-- Corollary 3.4 (i)–(v), p. 2283: for `t ∈ [0, T)`, convexity of `u ↦ J(t, x; u)` for some `x`,
for every `x`, convexity of `u ↦ J⁰(t, x; u)` (the cost of the data `d.hom`) for some `x`, for
every `x`, and `J⁰(t, 0; u) ≥ 0` on `𝒰[t, T]` are equivalent. Item (vi), `M₂(t) ≥ 0`, is not
stated (`M₂` comes from Proposition 3.1, cited from [30]). -/
theorem corollary_3_4 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d)
    (t : ℝ≥0) (ht : t < d.T) :
    List.TFAE [∃ x, IsConvexJ Bs d t x, ∀ x, IsConvexJ Bs d t x,
      ∃ x, IsConvexJ Bs d.hom t x, ∀ x, IsConvexJ Bs d.hom t x, IsNonnegJ0 Bs d t] := by sorry

end SLQSolv.MinSeq
