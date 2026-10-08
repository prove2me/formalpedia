-- Prove2me | Theorems.Thm_ParameterizedCalculus_family_comp_hasDerivAt
-- name    : ParameterizedCalculus.family_comp_hasDerivAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T14:51:32.279346+00:00
-- url     : https://prove2.me/theorems/ef66ca75-e149-44dc-8bad-03bd90a04cd5
-- title:
--   Chain rule for a parameter-dependent family along a differentiable curve
-- statement:
--   Let $E$ and $F$ be real normed vector spaces and let $f:\mathbb R\times E\to F$ be jointly smooth. If a curve $\gamma:\mathbb R\to E$ has derivative $a$ at $t$, then
--   $$\frac{d}{ds}\Big|_{s=t} f(s,\gamma(s))=\frac{d}{ds}\Big|_{s=t}f(s,\gamma(t))+D_xf(t,\gamma(t))a.$$
--   Only differentiability of the curve at the specified time is required. The two summands separate variation of the family from motion of its evaluation point. In Lemma 2.19 this is applied with $F=E^*$ to the moving one-form.
-- source:
--   Geiges, Contact geometry, Handbook of Differential Geometry II (2006), https://arxiv.org/abs/math/0307242, Lemma 2.19, pp. 13–14. This is the Banach-space coordinate-calculus ingredient of the one-form identity, rather than an additional theorem stated verbatim in the source.

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod

open scoped ContDiff

theorem ParameterizedCalculus.family_comp_hasDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → E → F)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2))
    (γ : ℝ → E) (t : ℝ) (γ' : E) (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => f s (γ s))
      (deriv (fun s => f s (γ t)) t + fderiv ℝ (f t) (γ t) γ') t := by sorry
