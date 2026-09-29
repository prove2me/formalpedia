-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_hauptmodulFive_of_not_modRepIsIrreducible
-- name    : WeierstrassCurve.exists_hauptmodulFive_of_not_modRepIsIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/1fb5e7d5-d498-5e83-a664-be001d3bada2
-- title:
--   Level-5 hauptmodul relation for mod-5 reducible curves
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, given by its five coefficients $a_1,a_2,a_3,a_4,a_6$, and suppose its discriminant satisfies $W.\Delta \neq 0$. Suppose further that the project's predicate `W.ModRepIsIrreducible 5` fails; by definition this predicate is `Affine.Point.GaloisRepIsIrreducible` for the base change $W_{\mathbb{Q}} =$ `W.map (Int.castRingHom ℚ)` taken over $\mathbb{Q}$ with coefficient field the algebraic closure $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, i.e. the conjunction of two conditions: that the $\mathbb{Z}$-torsion submodule `Submodule.torsionBy ℤ (W_ℚ⁄ℚ̄).Point 5` of points killed by $5$ is nontrivial, and that every $\mathbb{Z}/5$-submodule of it which is stable under the action of all field automorphisms $\sigma : \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ (acting on points by applying $\sigma$ to coordinates) equals $\bot$ or $\top$. Thus the hypothesis says that either the group of $5$-torsion points over $\overline{\mathbb{Q}}$ is trivial, or there exists a Galois-stable $\mathbb{Z}/5$-submodule of it different from $0$ and from the whole module. The conclusion is the existence of a rational number $v \neq 0$ with
--   $$(v^2 + 10v + 5)^3 \cdot \Delta_W = c_4(W)^3 \cdot v$$
--   as an identity in $\mathbb{Q}$, where $\Delta_W$ and $c_4(W)$ are the integer invariants of $W$ viewed in $\mathbb{Q}$. Since $j = c_4^3/\Delta$, this is the assertion that the $j$-invariant of $W$ is $(v^2+10v+5)^3/v$ for some nonzero rational $v$, stated as a polynomial identity so that no division and no nonvanishing of $c_4$ is required.
--
--   The relation expresses the classical genus-zero parametrisation of the modular curve $X_0(5)$ by a hauptmodul $v$, with $j = (v^2+10v+5)^3/v$: an elliptic curve over $\mathbb{Q}$ whose mod-$5$ representation is reducible, i.e. which admits a Galois-stable line in its $5$-torsion, gives a non-cuspidal rational point of $X_0(5)$ and hence such a value of $v$. The formal statement differs from the textbook version in being phrased for an integral Weierstrass model with $\Delta \neq 0$ rather than for an elliptic curve or a point of $X_0(5)$, in using the project's reducibility hypothesis as the failure of the stated irreducibility conjunction, and in recording the conclusion as an identity between $\Delta$ and $c_4^3$ rather than as an equation for $j$. It is used, together with the analogous level-$3$ relation, in [`WeierstrassCurve.fifteenIsogenyClassification`](thm.html#WeierstrassCurve.fifteenIsogenyClassification), which pins $c_4^3/\Delta$ down to one of four explicit rational values for curves reducible both mod $3$ and mod $5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_hauptmodulFive_of_not_modRepIsIrreducible.lean

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.exists_hauptmodulFive_of_not_modRepIsIrreducible (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (h5 : ¬ W.ModRepIsIrreducible 5) : ∃ v : ℚ, v ≠ 0 ∧ (v ^ 2 + 10 * v + 5) ^ 3 * (W.Δ : ℚ) = (W.c₄ : ℚ) ^ 3 * v := by sorry
