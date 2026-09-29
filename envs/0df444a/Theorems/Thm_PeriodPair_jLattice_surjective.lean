-- Prove2me | Theorems.Thm_PeriodPair_jLattice_surjective
-- name    : PeriodPair.jLattice_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/50646b81-ed3e-5faa-a8ed-15a3e3a886ef
-- title:
--   Surjectivity of the j-invariant of period pairs
-- statement:
--   The assertion is the proposition [`PeriodPair.JSurjective`](def/PeriodPair_Uniformization.html#L90): for every complex number $c$ there exists a period pair $L$ (an element of the type `PeriodPair`) such that, first, `L.DiscriminantNeZero` holds, i.e. the associated invariants satisfy $g_2(L)^3 - 27\,g_3(L)^2 \neq 0$, and second, `L.jLattice` equals $c$, where `jLattice` is by definition the quotient $$1728\,\frac{g_2(L)^3}{g_2(L)^3 - 27\,g_3(L)^2}.$$ There are no hypotheses and no parameters: the theorem is the bare statement that the function sending a period pair to this quotient of its invariants takes every value in $\mathbb{C}$, together with the non-vanishing of the discriminant expression at the witnessing period pair. The latter conjunct is in fact automatic, since the cited [`PeriodPair.discriminant_ne_zero`](thm.html#PeriodPair.discriminant_ne_zero) gives $g_2(L)^3 - 27\,g_3(L)^2 \neq 0$ for every period pair $L$, so the substance of the statement is the surjectivity of $L \mapsto$ `L.jLattice` onto $\mathbb{C}$.
--
--   This is the surjectivity of the modular $j$-invariant in the form needed for the analytic uniformisation of elliptic curves over $\mathbb{C}$: every complex number occurs as the $j$-invariant of a complex torus. It is used to produce, for a given Weierstrass curve over $\mathbb{C}$, a period pair with the same $j$-invariant, hence a change of variables matching the two curves, and it feeds into the computation of $j$-invariants attached to isogeny endomorphism data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_jLattice_surjective.lean

import Mathlib
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PeriodPair.jLattice_surjective : PeriodPair.JSurjective := by sorry
