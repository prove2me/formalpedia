-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_EF_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.EF_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:52.629285+00:00
-- url     : https://prove2.me/theorems/9db912b5-b7ad-4920-ac74-5cd2313d50c8
-- title:
--   Majorant Operators: EF eq
-- statement:
--   The Majorant Operators construction uses the EF eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L230-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L230-L239

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.EF_eq {z : Frame X.Ψ r} (hz : z ∈ X.dom) {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0)
    {μ ν : Fin r → E} (hμ : herm X.Gm μ ξ = 0) (hν : herm X.Gm ν ξ = 0) :
    ((EFf X.ξ0 X.Gm μ ν : ℚ) : ℝ) =
      gI z (Bop z (X.ucomp z ξ (X.embV μ))) (X.ucomp z ξ (X.embV ν)) := by sorry
