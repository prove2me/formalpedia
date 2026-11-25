-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_maj_eq_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.maj_eq_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:28:20.987074+00:00
-- url     : https://prove2.me/theorems/7e53918a-f358-455f-9ab6-94b2b6fa6a2e
-- title:
--   Torus At Data Pf: maj eq sum
-- statement:
--   The Torus At Data Pf construction uses the maj eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPfA.lean#L168-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPfA.lean#L168-L188

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
  (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
  (x : Frame X.Ψ r)
  (hflag : Submodule.span ℂ (Set.range fun a : Fin X.p0 => e (Fin.castLE X.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin X.p0 => X.colP x τ a))
  (hind : LinearIndependent ℂ (X.colP x τ))
include he hflag hind

theorem ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.maj_eq_sum (u : Fin r → ℂ) :
    X.maj x τ u = ∑ b : Fin r, ‖hermC τ.1 X.Gm u (e b)‖ ^ 2 := by sorry
