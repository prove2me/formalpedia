-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_expand
-- name    : ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:14.267886+00:00
-- url     : https://prove2.me/theorems/0d00dc3e-d826-4b07-8cc0-88f7f6226e16
-- title:
--   Torus At Data Pf: expand
-- statement:
--   The Torus At Data Pf construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPfA.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtDataPfA.lean#L44-L55

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
include he

theorem ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.expand (u : Fin r → ℂ) :
    u = ∑ a : Fin r, (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a)) • e a := by sorry
