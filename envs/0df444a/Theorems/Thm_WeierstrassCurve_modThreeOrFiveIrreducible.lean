-- Prove2me | Theorems.Thm_WeierstrassCurve_modThreeOrFiveIrreducible
-- name    : WeierstrassCurve.modThreeOrFiveIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/9e74441b-b5b3-58e8-a4b6-145fbbf4055c
-- title:
--   One of ρ̄_{W,3}, ρ̄_{W,5} is irreducible
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, i.e. a tuple of coefficients $a_1,a_2,a_3,a_4,a_6 \in \mathbb{Z}$, and assume two hypotheses: its discriminant satisfies $\Delta_W \neq 0$, and $W$ satisfies the project's predicate `IsSemistableModel`, which by definition says that for every prime number $p$ with $p \mid \Delta_W$ one has $p \nmid c_4(W)$ (so no prime divides both $\Delta_W$ and $c_4(W)$; no minimality or reduction-theoretic statement is involved). The conclusion is that `W.ModRepIsIrreducible 3` or `W.ModRepIsIrreducible 5` holds. Here `W.ModRepIsIrreducible n` is the project's notion: writing $W_{\mathbb{Q}}$ for the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$ and $\overline{\mathbb{Q}}$ for Mathlib's algebraic closure of $\mathbb{Q}$, consider the group of affine Weierstrass points of $W_{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$, its $n$-torsion submodule $\{P : nP = 0\}$ regarded as a module over $\mathbb{Z}/n$, and the action of the group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms obtained by applying an automorphism to the coordinates of a point. Then `ModRepIsIrreducible n` asserts (i) this $n$-torsion module is nontrivial, and (ii) every $\mathbb{Z}/n$-submodule of it that is stable under all these automorphisms is either $\bot$ or $\top$. Thus the theorem asserts: for $n = 3$ or for $n = 5$, the mod-$n$ torsion of $W_{\mathbb{Q}}$ is nonzero and has no Galois-stable submodule other than $0$ and the whole module. Nothing is claimed about the rank of the torsion module.
--
--   This is the $X_0(15)$ dichotomy used by Wiles to run the $3$–$5$ switch, appearing in Darmon–Diamond–Taylor as part of the proof of their Theorem 3.48. Compared with the textbook formulation for a semistable elliptic curve $E/\mathbb{Q}$, the formal statement works with an arbitrary integral Weierstrass model with $\Delta \neq 0$, takes semistability to be the purely arithmetic condition that no prime divides both $\Delta$ and $c_4$, and takes irreducibility to mean nontriviality of the $n$-torsion together with absence of proper nonzero Galois-stable $\mathbb{Z}/n$-submodules. It is the first step of the modularity half of the route: it feeds [`WeierstrassCurve.modularity_of_semistableModel`](thm.html#WeierstrassCurve.modularity_of_semistableModel), which in turn is used for [`FreyPackage.modularRepOfConductorLevel`](thm.html#FreyPackage.modularRepOfConductorLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_modThreeOrFiveIrreducible.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

theorem WeierstrassCurve.modThreeOrFiveIrreducible (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) : W.ModRepIsIrreducible 3 ∨ W.ModRepIsIrreducible 5 := by sorry
