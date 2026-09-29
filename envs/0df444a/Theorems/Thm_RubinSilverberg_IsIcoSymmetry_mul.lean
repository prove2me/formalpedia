-- Prove2me | Theorems.Thm_RubinSilverberg_IsIcoSymmetry_mul
-- name    : RubinSilverberg.IsIcoSymmetry.mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/7a6dbb95-ad84-50c4-8736-d4f378338fe2
-- title:
--   Icosahedral symmetries of the Rubin–Silverberg datum are closed under products
-- statement:
--   Let $K$ be a field of characteristic zero and let $g,h \in M_2(K)$ be two $2\times 2$ matrices, each satisfying the predicate `IsIcoSymmetry`, i.e. for $g$: $\det g = 1$; the three binary forms $V(n,d) = nd(n^{10}+11n^5d^5-d^{10})$, $H(n,d) = n^{20}-228n^{15}d^5+494n^{10}d^{10}+228n^5d^{15}+d^{20}$ and $T(n,d) = n^{30}+522n^{25}d^5-10005n^{20}d^{10}-10005n^{10}d^{20}-522n^5d^{25}+d^{30}$ (`kleinVHom`, `kleinHHom`, `kleinTHom`) are invariant under the substitution $(n,d) \mapsto (g_{00}n+g_{01}d,\ g_{10}n+g_{11}d)$, for all $n,d \in K$; and, for every $u \in K$ with $V(u) = u(u^{10}+11u^5-1) \neq 0$ (`kleinV`) and $j_g(u) := g_{10}u+g_{11} \neq 0$ (`moebDen`), writing $g\cdot u := (g_{00}u+g_{01})/j_g(u)$ (`moeb`), the two equalities $j_g(u)\,\beta(g\cdot u) = g_{00}\beta(u)+g_{01}\gamma(u)$ and $j_g(u)\,\gamma(g\cdot u) = g_{10}\beta(u)+g_{11}\gamma(u)$ hold, where $\beta =$ `rsBeta` and $\gamma =$ `rsGamma` are the explicit rational functions of the Rubin–Silverberg level-$5$ family. The conclusion is that the product matrix $g h$ again satisfies `IsIcoSymmetry`.
--
--   The statement expresses that the set of icosahedral symmetries of the Rubin–Silverberg datum is closed under matrix multiplication, so that a finite list of generating matrices suffices to produce the whole symmetry group acting on the parameter $u$ of the level-$5$ twist family. It is used in the verification that the third division polynomial of the associated Klein curve does not vanish at the relevant parameters ([`RubinSilverberg.kleinCurve_Psi3_eval_ne_zero`](thm.html#RubinSilverberg.kleinCurve_Psi3_eval_ne_zero)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RubinSilverberg_IsIcoSymmetry_mul.lean

import Definitions.Def_EllipticCurve_RubinSilverbergFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open RubinSilverberg

theorem RubinSilverberg.IsIcoSymmetry.mul {K : Type*} [Field K] [CharZero K] {g h : Matrix (Fin 2) (Fin 2) K} (hg : IsIcoSymmetry g) (hh : IsIcoSymmetry h) : IsIcoSymmetry (g * h) := by sorry
