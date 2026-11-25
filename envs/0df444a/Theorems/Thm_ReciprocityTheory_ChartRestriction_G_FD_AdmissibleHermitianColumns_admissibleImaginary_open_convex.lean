-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_admissibleImaginary_open_convex
-- name    : ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.admissibleImaginary_open_convex
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:08.412658+00:00
-- url     : https://prove2.me/theorems/d26fbc1d-7582-4664-8855-d5276a5db3d7
-- title:
--   Admissible Hermitian Columns: admissible Imaginary open convex
-- statement:
--   The Admissible Hermitian Columns construction uses the admissible Imaginary open convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/AdmissibleHermitianColumns.lean#L175-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/AdmissibleHermitianColumns.lean#L175-L179

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.admissibleImaginary_open_convex {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    IsOpen (admissibleImaginary X ξ x) ∧ Convex ℝ (admissibleImaginary X ξ x) := by sorry
