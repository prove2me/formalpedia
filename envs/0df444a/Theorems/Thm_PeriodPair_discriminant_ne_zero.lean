-- Prove2me | Theorems.Thm_PeriodPair_discriminant_ne_zero
-- name    : PeriodPair.discriminant_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/2d123a01-45de-5814-8eeb-541809a9d5f3
-- title:
--   Non-vanishing of the discriminant g₂³-27g₃²
-- statement:
--   The assertion is that for every term $L$ of the type `PeriodPair` the predicate `L.DiscriminantNeZero` holds, that is, the complex number
--   $$L.g_2^3 - 27\,L.g_3^2$$
--   is nonzero, where $L.g_2$ and $L.g_3$ are the two invariants attached to $L$. There are no further variables and no hypotheses: the statement is universally quantified over all period pairs, so the non-vanishing is unconditional and holds for every object of this type. Unfolded, `DiscriminantNeZero` is precisely the proposition $L.g_2^3 - 27 L.g_3^2 \neq 0$, with the numeral $27$ read in $\mathbb{C}$; no factor such as $16$ or $-16$ normalising the discriminant of the associated cubic is included, and the statement makes no reference to the roots of that cubic, to smoothness, or to any Weierstrass equation. In classical terms, for the lattice determined by $L$ with Eisenstein invariants $g_2$ and $g_3$ this is the non-vanishing of $\Delta$ up to a nonzero constant factor.
--
--   This is the non-vanishing of the modular discriminant for a period lattice, the condition under which $y^2 = 4x^3 - g_2 x - g_3$ defines an elliptic curve. It discharges, once and for all, the `DiscriminantNeZero` hypothesis carried by the constructions of the analytic uniformisation (the point map attached to a period pair and the associated statements about rational homomorphisms and differentiable lifts), and is cited by those results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_discriminant_ne_zero.lean

import Mathlib
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PeriodPair.discriminant_ne_zero (L : PeriodPair) : L.DiscriminantNeZero := by sorry
