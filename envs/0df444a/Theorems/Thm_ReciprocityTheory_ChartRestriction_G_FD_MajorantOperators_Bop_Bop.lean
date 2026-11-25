-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_Bop_Bop
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.Bop_Bop
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:56.623824+00:00
-- url     : https://prove2.me/theorems/94095d6d-7d23-48dd-8512-3b019cf9ae80
-- title:
--   Majorant Operators: Bop Bop
-- statement:
--   The Majorant Operators construction uses the Bop Bop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L272-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L272-L278

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.Bop_Bop {z : Frame Y.Ψ r} (hz : z ∈ Y.dom) (u : Y.Ψ → Fin r → ℂ) :
    Bop (X := Y.toData) z (Bop (X := Y.toData) z u) = (-(Y.k0 ^ 2) : ℝ) • u := by sorry
