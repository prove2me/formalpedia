-- Prove2me | Theorems.Thm_SmolenskyAC_easy_NOT_MODp
-- name    : SmolenskyAC.easy_NOT_MODp
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:56.810375+00:00
-- url     : https://prove2.me/theorems/f1805cb2-5057-4dc5-8709-9919707f3dc6
-- title:
--   NOT is $F$-easy for every field; $\mathrm{MOD}_p$ is $F$-easy in characteristic $p$
-- statement:
--   1. For every field $F$, $\mathrm{NOT}$ is $F$-easy with constant $1$: $\mathrm{NOT}(g)=1-g$.
--   2. For every prime $p$ and every field $F$ of characteristic $p$, $\mathrm{MOD}_p$ is $F$-easy with constant $p-1$:
--   $$\mathrm{MOD}_p(g_1,\dots,g_m)=\Big(\sum_{i=1}^m g_i\Big)^{p-1}.$$
--
--   These are the gates that cost nothing in degree, which is why the main theorem counts only AND and OR gates.
--
--   Differences from the source:
--   - generalization: NOT and MOD_p are F-easy (some constant λ) → NOT with λ = 1, MOD_p with λ = p − 1; reason: the polynomials 1 − g and (Σ g_i)^(p−1) given on the page; this implies the existence of a constant
--   - generalization: NOT takes one input → a NOT gate may have any fan-in and negates its first source (true with none); reason: a page NOT gate is the fan-in 1 case; the extra sources are ignored, and they only increase the depth
--   - encoding: a representation in U^n_F for Boolean functions g_1, …, g_m → an identity at every Boolean point z ∈ {0,1}^m; reason: pointwise these are the same identity
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, F-easy and Nearly F-easy Operations, the paragraph after the definition of F-easy, p.79 (pdf 3)

import Mathlib
import Definitions.Def_SmolenskyAC_Easy

namespace SmolenskyAC

universe u

/-- **NOT and `MOD_p` are `F`-easy** (Smolensky, STOC 1987, p.79, the paragraph after the
definition of `F`-easy): for any field `F`, `NOT(g) = 1 − g`, so NOT is `F`-easy (constant `1`);
and for a prime `p` and any field `F` of characteristic `p`,
`MOD_p(g_1, …, g_m) = (∑ g_i)^{p−1}`, so `MOD_p` is `F`-easy (constant `p − 1`). -/
theorem easy_NOT_MODp :
    (∀ (F : Type u) [Field F], IsFEasy F 1 NOT) ∧
    (∀ (p : ℕ) (F : Type u) [Field F] [CharP F p], p.Prime → IsFEasy F (p - 1) (MODp p)) := by sorry

end SmolenskyAC
