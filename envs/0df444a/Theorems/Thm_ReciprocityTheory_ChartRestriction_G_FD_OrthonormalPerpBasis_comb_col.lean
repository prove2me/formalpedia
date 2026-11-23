-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_comb_col
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.comb_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:23.942984+00:00
-- url     : https://prove2.me/theorems/f59c63b3-1618-4032-9bcc-d75e5e759a14
-- title:
--   Orthonormal Perp Basis: comb col
-- statement:
--   The Orthonormal Perp Basis construction uses the comb col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HCSumRight.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HCSumRight.lean#L59-L68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OnbPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosCoordNe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HCSumRight
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.comb_col {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c : Fin r → ℂ) (b : Fin r) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (col (mat x0 τ) b) = c b * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) := by sorry
