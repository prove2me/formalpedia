-- Prove2me | Theorems.Thm_TypeICutPointExists
-- name    : TypeICutPointExists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:04.448685+00:00
-- url     : https://prove2.me/theorems/e1455d99-b8bb-400c-9511-5b306cc9a789
-- title:
--   Type ICut Point Exists: Type ICut Point Exists
-- statement:
--   Paper Lemma 3.8's cut-point construction (paper.tex 798-838, proof 840-913), stated
--   existentially in `(t,t',β)` with no choice function (the paper's own "lexicographically smallest
--   attaining pair" carries no mathematical content and nothing downstream needs functionality): for
--   `0 < ε < 1`, `0 < δ`, and a closed, piecewise-geodesic curve `γ` that fails to be `(δ,ε)`-l.s.i.,
--   there exist `t,t' ∈ [0,γ.len]` and `β : ℝ` such that, writing `A := γ|_{[t,t']}` (`curveArc`) for
--   the counter-clockwise circular arc between them: `β` is simultaneously the arc's own length and
--   the circle distance `dGamma γ t t'` (these coincide because `β ≤ γ.len/2`, in either order of
--   `t,t'`); `β` lies in `[δ, γ.len/2]`; `t,t'` are moved apart by at most `ε*β`; and, whenever
--   `δ < β` (the genuinely non-degenerate case), `t,t'` are also moved apart by *at least* `ε*β`, the
--   arc `A` is not closed, and `A` itself is `(δ,ε)`-l.s.i.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/TypeICutPointExists.lean#L22-L231
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/TypeICutPointExists.lean#L22-L231

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_CurveArcEval
import Definitions.Def_Tablet_TypeICutMinimalPair
import Definitions.Def_Tablet_TypeICutPointExists
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_CurveArcEval
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_TypeICutMinimalPair

set_option autoImplicit false
open Set

theorem TypeICutPointExists {E : Type*} [MetricSpace E] (γ : Curve E)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ)
    (δ ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ)
    (hnlsi : ¬ IsLSI γ δ ε) :
    ∃ (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len) (β : ℝ),
      β = (curveArc γ hclosed t t' ht0 htl ht'0 ht'l).len ∧
      β = dGamma γ t t' ∧
      δ ≤ β ∧ β ≤ γ.len / 2 ∧
      dist (γ.toFun t) (γ.toFun t') ≤ ε * β ∧
      (δ < β → ε * β ≤ dist (γ.toFun t) (γ.toFun t')) ∧
      (δ < β → ¬ IsClosedCurve (curveArc γ hclosed t t' ht0 htl ht'0 ht'l)) ∧
      (δ < β → IsLSI (curveArc γ hclosed t t' ht0 htl ht'0 ht'l) δ ε) := by sorry
