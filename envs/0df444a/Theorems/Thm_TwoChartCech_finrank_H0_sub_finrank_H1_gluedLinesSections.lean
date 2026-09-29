-- Prove2me | Theorems.Thm_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections
-- name    : TwoChartCech.finrank_H0_sub_finrank_H1_gluedLinesSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/bb068d9b-7ca4-5c1f-82b9-909f1a2cdc6d
-- title:
--   Euler characteristic n+m+2-s for two glued lines
-- statement:
--   Let $k$ be a field, let $s$ be a natural number, and let $a, b, \mathrm{lam} : \mathrm{Fin}\,s \to k^\times$ be families of units with $a$ injective; let $n, m \in \mathbf{Z}$. Consider the two-chart Čech datum `gluedLinesSections k a b lam n m` over the cover `gluedLinesCover k a b`, whose rings are the subalgebra `gluedLinesOverlap k a b` of $k[T;T^{-1}] \times k[T;T^{-1}]$ and its intersections with `polyPart k` $\times$ `polyPart k` and with `invPolyPart k` $\times$ `invPolyPart k`, the restriction maps being the inclusions. Its modules are: $M_{01}$, the pairs $f = (f_1,f_2)$ of Laurent polynomials satisfying the predicate `GluedCond a b lam`; $M_0$, those $f$ in $M_{01}$ with both components in `polyPart k`; and $M_1$, those $f$ in $M_{01}$ with $f_1 \cdot T^{-n}$ and $f_2 \cdot T^{-m}$ in `invPolyPart k`, with $r_0, r_1$ the inclusions into $M_{01}$. Writing $\mathrm{H}^0$ for the kernel of the Čech differential $(f,g) \mapsto -r_0 f + r_1 g$ on $M_0 \times M_1$ and $\mathrm{H}^1$ for the cokernel $M_{01}$ modulo its image, the assertion is that $\mathrm{H}^0$ and $\mathrm{H}^1$ are finite-dimensional $k$-modules and that, as integers, $\dim_k \mathrm{H}^0 - \dim_k \mathrm{H}^1 = n + m + 2 - s$.
--
--   This is the Riemann–Roch, or Euler-characteristic, computation for a line bundle of multidegree $(n,m)$ with gluing parameters $\mathrm{lam}$ on two projective lines glued transversally at the $s$ distinct points determined by $a$ and $b$, presented entirely through the two-chart Čech complex of Laurent polynomials. It is used in the study of effective relative Cartier divisors and of the relative Picard group of such glued curves, for instance to compare $\dim_k \mathrm{H}^1$ with $\dim_k \mathrm{H}^0$ in the normalised case $(n,m) = (s-1,0)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections.lean

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TwoChartCech

universe u

theorem TwoChartCech.finrank_H0_sub_finrank_H1_gluedLinesSections
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) (n m : ℤ) :
    Module.Finite k ↥(gluedLinesSections k a b lam n m).H0 ∧
      Module.Finite k (gluedLinesSections k a b lam n m).H1 ∧
      (Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 : ℤ)
        - Module.finrank k (gluedLinesSections k a b lam n m).H1 = n + m + 2 - s := by sorry
