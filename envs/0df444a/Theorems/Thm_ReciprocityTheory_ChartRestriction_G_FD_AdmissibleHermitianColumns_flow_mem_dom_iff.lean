-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_flow_mem_dom_iff
-- name    : ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.flow_mem_dom_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:59.137801+00:00
-- url     : https://prove2.me/theorems/b949bddf-11cd-430d-a236-34927c06e4fe
-- title:
--   Admissible Hermitian Columns: flow mem dom iff
-- statement:
--   The Admissible Hermitian Columns construction uses the flow mem dom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/AdmissibleHermitianColumns.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/AdmissibleHermitianColumns.lean#L78-L87

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

theorem ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.flow_mem_dom_iff {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (x : Frame X.Ψ r)
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) :
    X.flow ξ s x ∈ X.dom ↔ (fun τ => (s τ).im) ∈ admissibleImaginary X ξ x := by sorry
