-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_Bop_self
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_Bop_self
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:43.144803+00:00
-- url     : https://prove2.me/theorems/6338a699-f757-5a26-8274-2b3a38660215
-- title:
--   Majorant Operators: g I Bop self
-- statement:
--   The Majorant Operators construction uses the g I Bop self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L262-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L262-L270

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
variable {Y : DataX E r}

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_Bop_self {z : Frame Y.Ψ r} (hz : z ∈ Y.dom) (u : Y.Ψ → Fin r → ℂ) :
    gI (X := Y.toData) z (Bop (X := Y.toData) z u) (Bop (X := Y.toData) z u) =
      Y.k0 ^ 2 * gI (X := Y.toData) z u u := by sorry
