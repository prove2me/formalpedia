-- Prove2me | Theorems.Thm_PGDMap20261031_pgd_best_modulus
-- name    : PGDMap20261031.pgd_best_modulus
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:00.17411+00:00
-- url     : https://prove2.me/theorems/46e7dbaa-4ba1-47cc-a82e-014143b669b9
-- title:
--   Attainment of the best strong-convexity modulus
-- statement:
--   ## Statement
--
--   Let $d\in\mathbb N$, including $d=0$, and let $E=\mathbb R^d$ with its Euclidean inner product and norm. A penalty datum is an arbitrary set $D\subseteq E$ and a total function $\rho:E\to\mathbb R$. Call it admissible when $D$ is nonempty, its epigraph $\{(z,a)\in E\times\mathbb R:z\in D,\ \rho(z)\le a\}$ is closed, and $\rho$ is convex on the convex set $D$. For $\eta\in\mathbb R$, say that $\rho$ has modulus $\eta$ on $D$ when, for all $a,b\in D$ and all real $t\in[0,1]$, $\rho(ta+(1-t)b)\le t\rho(a)+(1-t)\rho(b)-(\eta/2)t(1-t)\|a-b\|^2$. Write $m=\sup\{\eta\in\mathbb R:0\le\eta\ \text{and }\rho\text{ has modulus }\eta\text{ on }D\}$, using the total real supremum operation, whose value is $0$ for an empty or unbounded-above set. For every $d$ and every admissible $(D,\rho)$ whose domain contains two distinct points, $m\ge0$ and $\rho$ has modulus $m$ on $D$.
-- source:
--   Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty, manuscript dated 2026-10-30, Theorem 1 proof, p. 7; local source: 01_PGD_Exact_Residual_Curve.pdf

import Definitions.Def_PGDMap20261031_PGD
open PGDMap20261031

theorem PGDMap20261031.pgd_best_modulus : BestModulusClaim := by sorry
