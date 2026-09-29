-- Prove2me | Theorems.Thm_Rudin_ch10_simplex_ftc
-- name    : Rudin.ch10_simplex_ftc
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T03:06:43.692303+00:00
-- url     : https://prove2.me/theorems/eb77e780-b724-44d9-9135-27b35ad140cf
-- title:
--   Fundamental theorem of calculus on the simplex $Q^{k+1}$
-- statement:
--   Let $k\ge 0$, let $f:\mathbb{R}^{k+1}\to\mathbb{R}$ be of class $C'$, and fix a coordinate
--   direction $c\in\{1,\dots,k+1\}$. Write $Q^{k+1}=\{x: x_i\ge 0,\ \sum_i x_i\le 1\}$ for the standard
--   simplex, and for $y\in\mathbb{R}^{k}$ and $t\in\mathbb{R}$ let $\iota_c(t,y)\in\mathbb{R}^{k+1}$ be
--   the point whose $c$-th coordinate is $t$ and whose remaining coordinates, in their natural order,
--   are those of $y$. Then
--   $$\int_{Q^{k+1}} (D_c f)(x)\,dx=\int_{Q^{k}}\Big[f\big(\iota_c(1-\textstyle\sum_s y_s,\;y)\big)-f\big(\iota_c(0,y)\big)\Big]\,dy .$$
--
--   The two terms on the right are the integrals of $f$ over the two faces of $Q^{k+1}$ that are not
--   parallel to the $c$-th coordinate direction, parametrized by the projection that forgets the $c$-th
--   coordinate: the slanted face $\{x\ge 0,\ \sum_i x_i=1\}$ and the coordinate face $\{x_c=0\}$. The
--   remaining $k$ faces of $Q^{k+1}$ contain the $c$-th direction and contribute nothing.
--
--   The proof is Fubini's theorem in the $c$-th coordinate — for fixed $y\in Q^k$ the point
--   $\iota_c(t,y)$ lies in $Q^{k+1}$ exactly for $0\le t\le 1-\sum_s y_s$ — followed by the fundamental
--   theorem of calculus in the variable $t$. This identity is the analytic step in Rudin's proof of
--   Stokes' theorem on a simplex; all remaining steps there are determinants and orientation
--   bookkeeping.
--
--   Formalization note: integrals are Lebesgue integrals for the volume measure, which agree with the
--   Riemann integrals of Rudin's Definition 10.1 for the continuous integrands considered here, and
--   $\iota_c$ is Mathlib's `Fin.insertNth`.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, proof of Theorem 10.33, pp. 273-274 (the integration by the fundamental theorem of calculus over the simplex Q^{k+1}), together with Theorem 10.2 (iterated integrals)

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- The fundamental theorem of calculus on the standard simplex: the integral over `Q^{k+1}` of
the `c`-th partial derivative of a function of class `C'` is the difference of its integrals over
the two faces of `Q^{k+1}` transversal to the `c`-th coordinate direction. -/
theorem ch10_simplex_ftc (k : ℕ) (f : (Fin (k + 1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (c : Fin (k + 1)) :
    ∫ x in stdSimplex (k + 1), partialDeriv f c x
      = ∫ y in stdSimplex k,
          (f (Fin.insertNth (α := fun _ => ℝ) c (1 - ∑ s, y s) y)
            - f (Fin.insertNth (α := fun _ => ℝ) c 0 y)) := by sorry

end Rudin
