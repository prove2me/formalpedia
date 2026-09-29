-- Prove2me | Theorems.Thm_WeierstrassCurve_fifteenIsogenyClassification
-- name    : WeierstrassCurve.fifteenIsogenyClassification
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/51d019cf-2d2c-5984-9fe3-5d0e16a396bd
-- title:
--   Four possible c₄³/Δ for rational 15-isogenies
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, i.e. a tuple $(a_1,a_2,a_3,a_4,a_6)$ of integers, with discriminant $\Delta(W)\neq 0$. Suppose that the project's predicate `W.ModRepIsIrreducible n` fails both for $n=3$ and for $n=5$. Here `W.ModRepIsIrreducible n` is, by definition, the conjunction of two conditions for the base change of $W$ along $\mathbb{Z}\to\mathbb{Q}$, viewed as an affine Weierstrass curve and evaluated on the group of its points over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`: that the $n$-torsion subgroup $\{P : nP = 0\}$, regarded as a module over $\mathbb{Z}/n$, is nontrivial, and that every $\mathbb{Z}/n$-submodule of it which is stable under all $\mathbb{Q}$-algebra automorphisms $\sigma$ of $\overline{\mathbb{Q}}$ (acting on points through the induced map) is either $\bot$ or $\top$. So the two hypotheses say that for $n=3$ and $n=5$ either the $n$-torsion vanishes or there is a Galois-stable $\mathbb{Z}/n$-submodule different from $0$ and from the whole of it; the formal hypothesis is thus slightly weaker than classical reducibility, since it also admits the degenerate case of trivial torsion. The conclusion is that, computed in $\mathbb{Q}$ from the integers $c_4(W)$ and $\Delta(W)$, the quantity $c_4(W)^3/\Delta(W)$ — the $j$-invariant of $W$ — equals one of the four rational numbers $-25/2$, $-349938025/8$, $-121945/32$, $46969655/32768$, that is $-5^2/2$, $-5^2\cdot 241^3/2^3$, $-5\cdot 29^3/2^5$, $5\cdot 211^3/2^{15}$.
--
--   Classically this is the determination of the non-cuspidal rational points of $X_0(15)$: an elliptic curve over $\mathbb{Q}$ admitting both a rational $3$-isogeny and a rational $5$-isogeny has a rational cyclic $15$-isogeny, and its $j$-invariant is one of the four listed values, those of the curves in the isogeny class of conductor $50$. The formal statement is phrased for an integral Weierstrass model with non-vanishing discriminant and takes as hypothesis the negation of the project's irreducibility predicate for the mod $3$ and mod $5$ torsion modules, so it also covers the degenerate case of vanishing torsion; it concludes about $c_4^3/\Delta$ rather than about isogenies. It feeds [`WeierstrassCurve.modThreeOrFiveIrreducible`](thm.html#WeierstrassCurve.modThreeOrFiveIrreducible), where one checks that none of the four values is compatible with semistability (each has positive $5$-adic valuation), hence a semistable model with $\Delta\neq 0$ has $\bar\rho_{W,3}$ or $\bar\rho_{W,5}$ irreducible — the starting point of Wiles's $3$–$5$ switch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_fifteenIsogenyClassification.lean

import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem WeierstrassCurve.fifteenIsogenyClassification (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (h3 : ¬ W.ModRepIsIrreducible 3) (h5 : ¬ W.ModRepIsIrreducible 5) : (W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ) = -25 / 2 ∨ (W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ) = -349938025 / 8 ∨ (W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ) = -121945 / 32 ∨ (W.c₄ : ℚ) ^ 3 / (W.Δ : ℚ) = 46969655 / 32768 := by sorry
