-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_nfac_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.nfac_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:05.482553+00:00
-- url     : https://prove2.me/theorems/4dfc5d10-9151-464f-83c3-a255f13c65e5
-- title:
--   Bounded Section Algebra: nfac pos
-- statement:
--   The Bounded Section Algebra construction uses the nfac pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoundedSectionAlgebra.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoundedSectionAlgebra.lean#L34-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.nfac_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) : 0 < X.nfac la x := by sorry
