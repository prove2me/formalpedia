-- Prove2me | Theorems.Thm_PGDMap20261031_pgd_flat_segments
-- name    : PGDMap20261031.pgd_flat_segments
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:58.498957+00:00
-- url     : https://prove2.me/theorems/a34a13e9-4792-4bba-8893-b205933dafd8
-- title:
--   Lemma 3: asymptotically affine segments
-- statement:
--   ## Statement
--
--   Let $d\in\mathbb N$, including $d=0$, and let $E=\mathbb R^d$ with its Euclidean inner product and norm. A penalty datum is an arbitrary set $D\subseteq E$ and a total function $\rho:E\to\mathbb R$. Call it admissible when $D$ is nonempty, its epigraph $\{(z,a)\in E\times\mathbb R:z\in D,\ \rho(z)\le a\}$ is closed, and $\rho$ is convex on the convex set $D$. For $\eta\in\mathbb R$, say that $\rho$ has modulus $\eta$ on $D$ when, for all $a,b\in D$ and all real $t\in[0,1]$, $\rho(ta+(1-t)b)\le t\rho(a)+(1-t)\rho(b)-(\eta/2)t(1-t)\|a-b\|^2$. Write $m=\sup\{\eta\in\mathbb R:0\le\eta\ \text{and }\rho\text{ has modulus }\eta\text{ on }D\}$, using the total real supremum operation, whose value is $0$ for an empty or unbounded-above set. For every natural $d$ and admissible $(D,\rho)$ on $E=\mathbb R^d$ whose domain contains two distinct points and whose supremal modulus $m$ equals $0$, and for every real $M>0$ and $\varepsilon>0$, there exist $c,s,v\in E$ and real $\delta>0$ such that $c\in D$, $\rho(c)+\langle s,y-c\rangle\le\rho(y)$ for every $y\in D$, $\|v\|=1$, and for every real $t\in[-M,M]$, $c+\delta t v\in D$ and $0\le[\rho(c+\delta t v)-\rho(c)-\delta t\langle s,v\rangle]/\delta^2\le\varepsilon$. The witnesses may depend on both $M$ and $\varepsilon$.
-- source:
--   Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty, manuscript dated 2026-10-30, Lemma 3, p. 6; local source: 01_PGD_Exact_Residual_Curve.pdf

import Definitions.Def_PGDMap20261031_PGD
open PGDMap20261031

theorem PGDMap20261031.pgd_flat_segments : FlatSegmentsClaim := by sorry
