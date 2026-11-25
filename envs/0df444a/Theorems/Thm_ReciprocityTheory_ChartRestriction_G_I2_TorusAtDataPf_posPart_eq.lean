-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_posPart_eq
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.posPart_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:28:02.567631+00:00
-- url     : https://prove2.me/theorems/a2135c9f-b117-527f-84c7-cd479976b574
-- title:
--   Torus At Data Pf: pos Part eq
-- statement:
--   The Torus At Data Pf construction uses the pos Part eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPfA.lean#L129-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPfA.lean#L129-L165

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

theorem ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.posPart_eq (u : Fin r → ℂ) :
    X.posPart x τ u = ∑ a : Fin X.p0, ‖hermC τ.1 X.Gm u (e (Fin.castLE X.p0_le a))‖ ^ 2 := by sorry
