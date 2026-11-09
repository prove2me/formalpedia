-- Prove2me | Theorems.Thm_StochMatchPoly_lemma_4_4
-- name    : StochMatchPoly.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:18:55.383304+00:00
-- url     : https://prove2.me/theorems/4e0e8025-c197-42ed-b0e2-f587f579a71b
-- title:
--   Lemma 4.4 — repairing vertex loads by $y_{uv}=x_{uv}/\max\{1,x_u,x_v\}$
-- statement:
--   Let $K$ be a finite simple graph and $x$ a nonnegative edge vector on $K$, and put $y_{uv}=x_{uv}/\max\{1,x_u,x_v\}$. Then
--
--   1. $y$ is a fractional matching ($y\ge0$ and $y_v\le1$ for every vertex $v$);
--   2. $y$ has the same support as $x$: $y_e>0$ iff $x_e>0$ for every edge $e$;
--   3. $$|x|-|y|\le\sum_v(x_v-1)_+ ;$$
--   4. an edge of weight one whose endpoints both have load one retains weight one: if $x_{uv}=1$ and $x_u=x_v=1$ then $y_{uv}=1$.
--
--   The lemma turns the main proof's fractional assignment into a fractional matching, losing only the total overload.
--
--   Differences from the source:
--   - encoding: a nonnegative edge vector x (graphs of §4.1 are finite and simple) → x : Sym2 V → ℝ nonnegative on the edges of a finite SimpleGraph K; only its values on edges are used; reason: Lean convention; same instances
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), Lemma 4.4, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_StochMatchPoly_load

open Classical

namespace StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), Lemma 4.4 (Repairing vertex loads), p.10 (PDF p.11).

"For any nonnegative edge vector x, put y_uv = x_uv / max{1, x_u, x_v}. Then y is a fractional
matching on the same support and |x| − |y| ≤ Σ_v (x_v − 1)₊. An edge of weight one whose
endpoints both have load one retains weight one."

**Formalization Note.** `K` is a finite simple graph (§4.1); `x` is nonnegative on its edges, and
`y = repair K x`. "On the same support": for every edge, `y_e > 0` iff `x_e > 0`. `(r)₊` is
`max r 0`. The four conclusions are the four conjuncts. -/
theorem lemma_4_4 {V : Type*} [Fintype V] (K : SimpleGraph V) (x : Sym2 V → ℝ)
    (hx : ∀ e ∈ K.edgeFinset, 0 ≤ x e) :
    IsFracMatching K (repair K x) ∧
      (∀ e ∈ K.edgeFinset, 0 < repair K x e ↔ 0 < x e) ∧
      total K x - total K (repair K x) ≤ ∑ v, max (load K x v - 1) 0 ∧
      ∀ u v, K.Adj u v → x s(u, v) = 1 → load K x u = 1 → load K x v = 1 →
        repair K x s(u, v) = 1 := by sorry

end StochMatchPoly
