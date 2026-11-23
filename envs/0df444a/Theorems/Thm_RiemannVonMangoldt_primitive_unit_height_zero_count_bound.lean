-- Prove2me | Theorems.Thm_RiemannVonMangoldt_primitive_unit_height_zero_count_bound
-- name    : RiemannVonMangoldt.primitive_unit_height_zero_count_bound
-- status  : Open
-- author  : @phi9t
-- created : 2026-11-23T05:49:55.84336+00:00
-- url     : https://prove2.me/theorems/17f9c6f3-6197-4921-be42-f14b994f346f
-- title:
--   Explicit unit-height increment bound for primitive Dirichlet L-function zero counts
-- statement:
--   Let $q$ be a positive integer and let $\chi$ be a primitive Dirichlet character modulo $q$. Write $N_\chi(U)$ for the existing Dirichlet zero-counting function, the sum of the natural analytic-order weights of the zeros of $L(s,\chi)$ in
--   $$
--   0<\operatorname{Re}s<1,\qquad |\operatorname{Im}s|\le U.
--   $$
--   For every real $T\ge8$,
--   $$
--   0\le N_\chi(T+1)-N_\chi(T)
--   \le1900+50\log q+110\log(T+2).
--   $$
--
--   The increment includes both signs of the imaginary part. Its shell is $T<|\operatorname{Im}s|\le T+1$, with the lower boundary excluded and the upper boundary included. The modulus is unrestricted apart from $q\ne0$, and the primitive principal character of conductor one is included.
--
--   This is an explicit local increment estimate for the published counting function, useful when moving a Dirichlet zero-counting height through one unit interval. It does not assert a Riemann–von Mangoldt asymptotic formula or a Riemann hypothesis.
--
--   **Formalization Note.** The count is exactly RiemannVonMangoldt.dirichletZeroCount from the public ZeroCounts definition. Its weights are real casts of analyticOrderNatAt, whose natural-valued convention sends infinite analytic order to zero. The statement assumes neither finite support nor an analytic band estimate. The numerical constants are inherited from the accepted Helfgott finite-set band estimate.
-- source:
--   Count-and-signed-shell integration of the existing public RiemannVonMangoldt_ZeroCounts definition (UUID 6e00e685-a716-48b3-b245-c1d6406c8f76) with Helfgott.regularized_primitive_strip_band_multiplicity_logarithmic_bound, https://prove2.me/theorems/c747ca4e-9a8c-4e92-bd74-412f0e780b7a, accepted proof by raresbuhai, submission 9dbbc65e-3060-43ec-9421-f689bf5ae363. The numerical band bound and all constants are credited to that theorem. Compact-zero finiteness and preservation of analytic order under principal-character regularization also occur in the earlier accepted proof by moona3k of GoldbachDirichletZeros.compact_occurrence_enumeration, https://prove2.me/theorems/9d4fb358-c442-42f8-a340-4d537f3cf7bd, submission be1e360a-903b-4af7-b073-f3c33d27044f; those principles are not claimed as new. The contribution here is the unconditional connection to the exact original finsum count through its strict-left, closed-right signed shell. This is an auxiliary result for RiemannVonMangoldt.dirichlet_L_zero_count, https://prove2.me/theorems/2662b9ff-2c43-4ab9-a198-f989ab875fb8.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts

set_option autoImplicit false

theorem RiemannVonMangoldt.primitive_unit_height_zero_count_bound
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (T : ℝ) (hT : 8 ≤ T) :
    0 ≤ RiemannVonMangoldt.dirichletZeroCount χ (T + 1) -
      RiemannVonMangoldt.dirichletZeroCount χ T ∧
    RiemannVonMangoldt.dirichletZeroCount χ (T + 1) -
      RiemannVonMangoldt.dirichletZeroCount χ T ≤
        1900 + 50 * Real.log (q : ℝ) + 110 * Real.log (T + 2) := by sorry
