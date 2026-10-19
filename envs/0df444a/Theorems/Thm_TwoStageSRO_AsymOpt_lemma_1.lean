-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_lemma_1
-- name    : TwoStageSRO.AsymOpt.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:43.18025+00:00
-- url     : https://prove2.me/theorems/e92b4679-6fa0-4caf-b8a6-01e284dc1f22
-- title:
--   Lemma 1, p. 14 — conditions [A4], [A5] and [A6] are equivalent
-- statement:
--   For a two-stage problem with polyhedron $\Xi$ and any $\ell_p$-norm, the following conditions are equivalent:
--
--   1. [A4] there are $x$ and $\epsilon>0$ such that around every $\hat\zeta\in\Xi$ some linear decision rule is feasible on $B(\hat\zeta,\epsilon)\cap\Xi$;
--   2. [A5] there are $x$ and $\epsilon>0$ with $Q(x,\zeta)<\infty$ on $\Xi$ and, for each minimal face $F$ of $\Xi$, a recourse matrix $Y^F$ with $Q^{\{Y^F\}}_\epsilon(x,\zeta)<\infty$ for all $\zeta\in F$;
--   3. [A6] there are $x$, $\epsilon>0$ and a finite set $\mathcal C$ of recourse matrices with $Q^{\mathcal C}_\epsilon(x,\zeta)<\infty$ for all $\zeta\in\Xi$.
--
--   $$\text{[A4]}\iff\text{[A5]}\iff\text{[A6]}.$$
--
--   [A5] gives a checkable criterion for the main theorem's hypothesis [A4]; [A6], with finitely many recourse matrices, is the form used in the proof of the main theorem.
--
--   **Formalization Note** Stated as `List.TFAE [A4 M p, A5 M p, A6 M p]`. Minimal faces are inclusion-minimal nonempty faces.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 14, Lemma 1

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 14, Lemma 1:
conditions [A4], [A5] and [A6] are equivalent.

**Formalization Note** [A4], [A5], [A6] are `A4`, `A5`, `A6` (p. 12 and p. 14), for an arbitrary
`ℓp`-norm. Minimal faces are inclusion-minimal nonempty sets `{ζ ∈ Ξ : G_I ζ = g⁰_I}`. -/
theorem lemma_1 {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    List.TFAE [A4 M p, A5 M p, A6 M p] := by sorry

end TwoStageSRO.AsymOpt
