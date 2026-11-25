-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scale_sImg_expr
-- name    : ReciprocityTheory.ChartRestriction.G.T0.scale_sImg_expr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:58.018096+00:00
-- url     : https://prove2.me/theorems/76ba2c99-e6a1-4d7f-9218-f26fc01aef03
-- title:
--   T0: scale s Img expr
-- statement:
--   The T0 construction uses the scale s Img expr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L102-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L102-L140

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.scale_sImg_expr (b : Fin (D + 1)) (hb : b ≠ 0) (u : Ωˣ) (j₀ : Fin (N + 1))
    (x : Fin N → Ω) (p : TVar D N) :
    scaleEquiv (InBlock (D := D) (N := N) b) u
      (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
        (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
          else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
        (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2) =
      (if p.1 = b then C (u : Ω) else 1) *
      Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
        (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
          else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
        (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2 := by sorry
