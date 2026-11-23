-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_maj_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.maj_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:16.747786+00:00
-- url     : https://prove2.me/theorems/65bff642-9eb9-437b-88e7-e1a23b5eb753
-- title:
--   Majorant Operators: maj nonneg
-- statement:
--   The Majorant Operators construction uses the maj nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MajorantOperators.lean#L51-L55

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

theorem ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.maj_nonneg {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj z τ v := by sorry
