-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_comb_comb
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.comb_comb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:20:08.158436+00:00
-- url     : https://prove2.me/theorems/5263895b-6fb1-4ff4-92c7-6133f19967c9
-- title:
--   Orthonormal Perp Basis: comb comb
-- statement:
--   The Orthonormal Perp Basis construction uses the comb comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HCSumRight.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HCSumRight.lean#L75-L80

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

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.comb_comb {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c d : Fin r → ℂ) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (∑ b, d b • col (mat x0 τ) b) =
      ∑ a, c a * conj (d a) * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by sorry
