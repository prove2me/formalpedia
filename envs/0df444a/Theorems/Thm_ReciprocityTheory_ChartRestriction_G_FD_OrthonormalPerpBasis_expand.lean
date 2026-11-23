-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_expand
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:25.82944+00:00
-- url     : https://prove2.me/theorems/16bfc7a0-f38b-444d-bdc3-4f7e352d41df
-- title:
--   Orthonormal Perp Basis: expand
-- statement:
--   The Orthonormal Perp Basis construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PosCoordNe.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PosCoordNe.lean#L46-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosCoordNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.expand {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → ℂ) :
    v = ∑ a : Fin r, (((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * hermC τ.1 X.Gm v (col (mat x τ) a)) • col (mat x τ) a := by sorry
