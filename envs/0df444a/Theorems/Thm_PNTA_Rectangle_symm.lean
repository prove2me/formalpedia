-- Prove2me | Theorems.Thm_PNTA_Rectangle_symm
-- name    : PNTA.Rectangle.symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T05:45:20.248431+00:00
-- url     : https://prove2.me/theorems/7868c44d-0f08-4576-9b06-8302922f0b95
-- title:
--   A rectangle is unchanged by swapping its opposite corners
-- statement:
--   The rectangle determined by two opposite corners does not depend on which corner is named first:
--   $$\mathrm{Rectangle}(z, w) \;=\; \mathrm{Rectangle}(w, z).$$
--
--   Here the rectangle is the product of the real interval spanned by $\mathrm{Re}\, z$ and $\mathrm{Re}\, w$ with the imaginary interval spanned by $\mathrm{Im}\, z$ and $\mathrm{Im}\, w$; since each coordinate interval is defined by its endpoints regardless of order, the set is symmetric in its two arguments. This lets an argument normalise the orientation of a rectangle without loss of generality.
--
--   **Formalization Note** The underlying intervals are the unordered ones, so the symmetry holds with no hypotheses relating $z$ and $w$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L19-L21

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone

open Complex Set Topology
open scoped Interval
variable {z w : ℂ} {c : ℝ}

theorem PNTA.Rectangle.symm : Rectangle z w = Rectangle w z := by sorry
