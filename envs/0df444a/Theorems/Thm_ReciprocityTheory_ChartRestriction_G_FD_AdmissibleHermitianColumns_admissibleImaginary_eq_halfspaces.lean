-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_admissibleImaginary_eq_halfspaces
-- name    : ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.admissibleImaginary_eq_halfspaces
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:14.262891+00:00
-- url     : https://prove2.me/theorems/32eecf18-fdaa-4424-b136-5c6dc4bab844
-- title:
--   Admissible Hermitian Columns: admissible Imaginary eq halfspaces
-- statement:
--   The Admissible Hermitian Columns construction uses the admissible Imaginary eq halfspaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/AdmissibleHermitianColumns.lean#L151-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/AdmissibleHermitianColumns.lean#L151-L173

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

theorem ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.admissibleImaginary_eq_halfspaces {ξ : Fin r → E} (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    ∃ a b : X.Ψ → Fin (r + 1) → ℝ, admissibleImaginary X ξ x = {y | ∀ τ i, 0 < a τ i + y τ * b τ i} := by sorry
