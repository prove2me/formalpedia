-- Prove2me | Theorems.Thm_PachDeZeeuw_Algebraic_bezout
-- name    : PachDeZeeuw.Algebraic.bezout
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T01:36:49.229766+00:00
-- url     : https://prove2.me/theorems/bc953983-eaa2-4bfc-a2b8-8408c911ce6c
-- title:
--   Finite-intersection B\u00e9zout bound for real plane curves (existential form)
-- statement:
--   There are no hypotheses: the theorem asserts the proposition `BezoutFiniteIntersectionStatement`, namely: for all degree bounds $d_1, d_2 \in \mathbb{N}$ there exists a constant $C \in \mathbb{N}$ with $0 < C$ such that for all sets $C_1, C_2 \subseteq \mathrm{Point2}$ satisfying $\mathrm{IsBoundedDegreeCurve}\,d_1\,C_1$, $\mathrm{IsBoundedDegreeCurve}\,d_2\,C_2$ and $\mathrm{NoCommonCurveComponent}\,C_1\,C_2$,
--
--   $$(C_1 \cap C_2).\mathrm{Finite} \;\land\; (C_1 \cap C_2).\mathrm{ncard} \le C.$$
--
--   Here $\mathrm{IsBoundedDegreeCurve}\,d\,C$ means that $C$ is the real zero set $\mathrm{PlaneCurveZeroSet}\,p$ of some nonzero bivariate real polynomial $p$ of total degree at most $d$, and $\mathrm{NoCommonCurveComponent}\,C_1\,C_2$ means that there is no *infinite* irreducible real curve (the real zero set of an irreducible polynomial) contained in both $C_1$ and $C_2$.
--
--   This is a weaker variant of Theorem 2.1 of Pach--de Zeeuw, in two respects. (a) The conclusion only asserts that some degree-dependent constant $C$ exists; the proof supplies the witness $C = (d_1 + d_2 + 1)^8 + 1$ and does not give the sharp count $d_1 d_2$. (b) The hypothesis is weaker than the paper's "no common factor": it only excludes a shared irreducible factor whose real zero set is infinite. A shared irreducible factor with a finite real zero set (for example $x^2 + y^2$, whose real zero set is the origin) is allowed by the Lean hypothesis but not by the paper's hypothesis. The explicit bounds are proved in `factorized_bezout_bound` and `irreducible_pair_intersection_bound`; this theorem only packages them into the existential form.
-- source:
--   Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), Theorem 2.1 (Bézout's inequality), in a weaker variant: existential degree-dependent constant instead of d1*d2, and hypothesis 'no common infinite irreducible component' instead of 'no common factor'; formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L1321-L1340

import Mathlib
import Definitions.Def_PdzBezout
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

theorem PachDeZeeuw.Algebraic.bezout : BezoutFiniteIntersectionStatement := by sorry
