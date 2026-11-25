-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_le_of_mem_support_mHom
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_of_mem_support_mHom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:10:24.444547+00:00
-- url     : https://prove2.me/theorems/0fb799e0-63d7-46fc-ac22-e187e20ff1c6
-- title:
--   Arakelov Geometry: le of mem support m Hom
-- statement:
--   The Arakelov Geometry construction uses the le of mem support m Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SupportSubsetMonoBox.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SupportSubsetMonoBox.lean#L11-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_of_mem_support_mHom {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : m ∈ f.support) (p : Σ k, ι k) : m p ≤ a p.1 := by sorry
