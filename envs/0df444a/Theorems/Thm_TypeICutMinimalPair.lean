-- Prove2me | Theorems.Thm_TypeICutMinimalPair
-- name    : TypeICutMinimalPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:28.276914+00:00
-- url     : https://prove2.me/theorems/4ac42270-17bf-4230-9371-2547ab74ef3c
-- title:
--   Type ICut Minimal Pair: Type ICut Minimal Pair
-- statement:
--   Attainment of the paper's infimum (paper.tex 852-864) at a pair of at most half the total
--   length. Let `γ` be a closed curve and let `S` be the set of pairs `(a,b) ∈ [0,γ.len]²` that are
--   `δ`-separated in the circle distance (`δ ≤ dGamma γ a b`) and `ε`-contracted by `γ`
--   (`dist (γ a) (γ b) ≤ ε * dGamma γ a b`); `S` is assumed non-empty, witnessed by `(a₀,b₀)`. Then the
--   counter-clockwise arc length `ℓ(a,b) := b - a` if `a ≤ b`, `(γ.len - a) + b` otherwise, attains a
--   minimum over `S`: there is `(t,t') ∈ S` with `ℓ(t,t') ≤ ℓ(a,b)` for every `(a,b) ∈ S`, and moreover
--   `δ ≤ ℓ(t,t') ≤ γ.len/2`. No order relation between `t` and `t'` is asserted: the minimizing pair
--   may have `t' < t`, i.e. the arc from `t` to `t'` may be the wrap-around one.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/TypeICutMinimalPair.lean#L15-L154
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/TypeICutMinimalPair.lean#L15-L154

import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_TypeICutMinimalPair
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open Set

theorem TypeICutMinimalPair {E : Type*} [MetricSpace E] (γ : Curve E)
    (hcl : IsClosedCurve γ) (δ ε : ℝ) (hδ : 0 < δ)
    (a₀ b₀ : ℝ) (ha₀ : a₀ ∈ Set.Icc (0 : ℝ) γ.len) (hb₀ : b₀ ∈ Set.Icc (0 : ℝ) γ.len)
    (hsep₀ : δ ≤ dGamma γ a₀ b₀)
    (hcon₀ : dist (γ.toFun a₀) (γ.toFun b₀) ≤ ε * dGamma γ a₀ b₀) :
    ∃ t t' : ℝ, t ∈ Set.Icc (0 : ℝ) γ.len ∧ t' ∈ Set.Icc (0 : ℝ) γ.len ∧
      δ ≤ dGamma γ t t' ∧
      dist (γ.toFun t) (γ.toFun t') ≤ ε * dGamma γ t t' ∧
      δ ≤ (if t ≤ t' then t' - t else (γ.len - t) + t') ∧
      (if t ≤ t' then t' - t else (γ.len - t) + t') ≤ γ.len / 2 ∧
      (∀ a ∈ Set.Icc (0 : ℝ) γ.len, ∀ b ∈ Set.Icc (0 : ℝ) γ.len,
        δ ≤ dGamma γ a b → dist (γ.toFun a) (γ.toFun b) ≤ ε * dGamma γ a b →
          (if t ≤ t' then t' - t else (γ.len - t) + t')
            ≤ (if a ≤ b then b - a else (γ.len - a) + b)) := by sorry
