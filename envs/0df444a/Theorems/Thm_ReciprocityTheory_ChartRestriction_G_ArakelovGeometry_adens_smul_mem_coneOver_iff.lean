-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_smul_mem_coneOver_iff
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_smul_mem_coneOver_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:13:06.864421+00:00
-- url     : https://prove2.me/theorems/06e91c78-8cdf-417b-a460-bdbd334b6569
-- title:
--   Arakelov Geometry: adens smul mem cone Over iff
-- statement:
--   The Arakelov Geometry construction uses the adens smul mem cone Over iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStA.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStA.lean#L23-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
variable {J : Type} [Fintype J] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_smul_mem_coneOver_iff {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → J → ℂ} {z : J → ℂ}
    {c : ℂ} (hc : c ≠ 0) : c • z ∈ coneOver U γ ↔ z ∈ coneOver U γ := by sorry
