-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_gramPos_det_ne
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.gramPos_det_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:27:56.022396+00:00
-- url     : https://prove2.me/theorems/7609b312-9010-4fd0-9672-5d57d1f7ce43
-- title:
--   Torus At Data Pf: gram Pos det ne
-- statement:
--   The Torus At Data Pf construction uses the gram Pos det ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPfA.lean#L97-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPfA.lean#L97-L126

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

theorem ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.gramPos_det_ne : (X.gramPos x τ).det ≠ 0 := by sorry
