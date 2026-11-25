-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_Bop_left
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_Bop_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:49.945786+00:00
-- url     : https://prove2.me/theorems/de32643f-8bf8-45ed-b2a9-ea2ac7e0062f
-- title:
--   Majorant Operators: g I Bop left
-- statement:
--   The Majorant Operators construction uses the g I Bop left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L146-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L146-L150

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_Bop_left {z : Frame X.Ψ r} (hz : z ∈ X.dom) (u v : X.Ψ → Fin r → ℂ) :
    gI z (Bop z u) v = ∑ τ, (2 * τ.1 (-X.ξ0) * hermC τ.1 X.Gm (u τ) (v τ)).re := by sorry
