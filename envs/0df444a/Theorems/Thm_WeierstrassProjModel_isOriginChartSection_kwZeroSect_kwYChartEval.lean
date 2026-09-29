-- Prove2me | Theorems.Thm_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval
-- name    : WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/3c6f83c9-9c13-5ce5-a897-3fd6cecff5e5
-- title:
--   Zero section lies in the origin chart, with vanishing coordinates
-- statement:
--   Let $T$ be a commutative ring and let $W$ be a Weierstrass cubic over $T$ in projective form, so that $W$ determines the homogeneous ideal $\mathrm{span}\{W.\mathrm{polynomial}\}$ in $T[X_0,X_1,X_2]$, the quotient ring `ProjModelRingCR` with its induced grading `projModelGradingCR`, and the structure morphism `projModelStrCR` from the associated `Proj` to $\operatorname{Spec} T$. Write $\chi$ for `kwYChartEval`, the ring homomorphism from the degree-zero homogeneous localization of the graded quotient away from the class of $X_1$ to $T$ obtained by lifting the evaluation $X \mapsto (0,1,0)$ (legitimate on the quotient because the Weierstrass cubic vanishes at $(0:1:0)$, and invertible on the localized element because the class of $X_1$ evaluates to $1$). The theorem asserts three things. First, `kwZeroSect`, the section of `projModelStrCR` over $\operatorname{Spec} T$ built from $\chi$, is an origin-chart section for $\chi$: its underlying morphism of schemes equals $\operatorname{Spec}$ of $\chi$ followed by the origin chart immersion $\mathrm{Proj}$-away inclusion at the degree-one element $X_1$. Second and third, $\chi$ kills the two chart coordinates $X_0/X_1$ and $X_2/X_1$, i.e. `xOverY` and `zOverY` both map to $0$.
--
--   This records that the point $(0:1:0)$ of the projective Weierstrass model is cut out by evaluation at $(0,1,0)$ on the chart $X_1 \neq 0$, and that in the coordinates $X_0/X_1$, $X_2/X_1$ of that chart the zero section sits at the origin. It is the starting point for work in the origin chart — formal-group and group-law computations on the Weierstrass model — and is used in the construction of level structures on modular curves, for instance in the full-level and Tate-point arguments that invoke origin charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_isOriginChartSection_kwZeroSect_kwYChartEval.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassProjModel.isOriginChartSection_kwZeroSect_kwYChartEval
    {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T) :
    IsOriginChartSection (kwZeroSect T W.toAffine) (kwYChartEval T W.toAffine) ∧
      kwYChartEval T W.toAffine (xOverY W) = 0 ∧ kwYChartEval T W.toAffine (zOverY W) = 0 := by sorry
