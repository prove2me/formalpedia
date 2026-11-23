-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_smul_fam_mem
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.smul_fam_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:06.127232+00:00
-- url     : https://prove2.me/theorems/b2c855c4-9fb6-49bc-b6d4-6b7e27373e22
-- title:
--   Majorant Operators: smul fam mem
-- statement:
--   The Majorant Operators construction uses the smul fam mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L85-L89

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.smul_fam_mem {z : Frame X.Ψ r} {ξ : Fin r → E} (s : X.Ψ → ℂ) {u : X.Ψ → Fin r → ℂ}
    (hu : u ∈ X.Uz z ξ) : (fun τ => s τ • u τ) ∈ X.Uz z ξ := by sorry
