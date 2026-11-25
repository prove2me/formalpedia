-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOrthogonality_herm_coord
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality.herm_coord
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:33:29.800452+00:00
-- url     : https://prove2.me/theorems/cebf3f95-7aef-56dd-b77d-d578b74456fa
-- title:
--   Majorant Orthogonality: herm coord
-- statement:
--   The Majorant Orthogonality construction uses the herm coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOrthogonality.lean#L130-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOrthogonality.lean#L130-L142

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearMaximum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCombinations
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantOrthogonality.herm_coord (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ)
    (u v : Fin r → E) : τ.1 (herm X.Gm u v) = ReciprocityTheory.MultiplicativeHeights.jForm X.p0
      ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 u) := by sorry
