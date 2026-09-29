-- Prove2me | Theorems.Thm_VectorSpaceOpt_rs_integral_exists_of_continuous
-- name    : VectorSpaceOpt.rs_integral_exists_of_continuous
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T03:16:25.981558+00:00
-- url     : https://prove2.me/theorems/36ed7b5f-6abb-4c01-9104-42cf6c4490d6
-- title:
--   Existence of $\int_a^b x\,dv$ for continuous $x$ and $v$ of bounded variation
-- statement:
--   Let $v$ be of bounded variation on $[a,b]$ and let $x$ be continuous on $[a,b]$. Then the Riemann–Stieltjes integral
--
--   $$\int_a^b x(t)\,dv(t)$$
--
--   exists: there is a real number $I$ such that every tagged Riemann–Stieltjes sum of sufficiently small mesh is within $\varepsilon$ of $I$.
--
--   This is the classical existence theorem pairing $C[a,b]$ with $BV[a,b]$. The proof is a Cauchy criterion driven by refinement: if $\omega$ bounds the oscillation of $x$ over intervals of length $\delta$, then for any tagged partition $P$ of mesh at most $\delta$ and any refinement $R$ of $P$ one has $|S(P)-S(R)|\le\omega\cdot \mathrm{T.V.}(v)$, because within each cell of $P$ the two tags differ by at most $\omega$ and the corresponding increments of $v$ sum in absolute value to at most the total variation. Passing through the common refinement of two partitions gives $|S(P)-S(P')|\le 2\omega\cdot\mathrm{T.V.}(v)$, and uniform continuity of $x$ on the compact interval makes $\omega\to0$ with the mesh.
--
--   Mathlib has no Riemann–Stieltjes integral, so this statement (with `VectorSpaceOpt_is_rs_integral` as the definition) is the entry point for anything built on the pairing — in particular for the Riesz representation theorem for $C[a,b]$.
--
--   **Formalization note.** The integrand is given as an element of $C([a,b],\mathbb{R})$ and extended to $\mathbb{R}$ by `Set.IccExtend`, which is constant outside $[a,b]$; only its values on $[a,b]$ are ever used, since all partition points lie in $[a,b]$.
-- source:
--   D. G. Luenberger, Optimization by Vector Space Methods, Wiley 1969, §5.5, pp. 113-115 (Riesz representation for C[a,b]); the Riemann-Stieltjes facts are the standard ones, e.g. T. M. Apostol, Mathematical Analysis, 2nd ed., Ch. 7, Theorems 7.19 and 7.27.

import Mathlib
import Definitions.Def_VectorSpaceOpt_bv_stieltjes

namespace VectorSpaceOpt

theorem rs_integral_exists_of_continuous (a b : ℝ) (hab : a ≤ b) (v : ℝ → ℝ)
    (hv : BoundedVariationOn v (Set.Icc a b)) (x : C(Set.Icc a b, ℝ)) :
    ∃ I : ℝ, VectorSpaceOpt_is_rs_integral (Set.IccExtend hab x) v a b I := by sorry

end VectorSpaceOpt
