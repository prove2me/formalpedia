-- Prove2me | Theorems.Thm_P2M_RH_ReciprocityTheory_ChartRestriction_G_T0_Data_wx_mem_c320beb591cc62f2
-- name    : P2M_RH_ReciprocityTheory_ChartRestriction_G_T0_Data_wx_mem_c320beb591cc62f2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:35.0257+00:00
-- url     : https://prove2.me/theorems/c1bba6d5-3d79-5eb3-a5c8-a0baed924072
-- title:
--   P2 M RH Reciprocity Theory Chart Restriction G T0 Data wx mem c320beb591cc62f2: P2 M RH Reciprocity Theory Chart Restriction G T0 Data wx mem c320beb591cc62f2
-- statement:
--   The P2 M RH Reciprocity Theory Chart Restriction G T0 Data wx mem c320beb591cc62f2 construction uses the P2 M RH Reciprocity Theory Chart Restriction G T0 Data wx mem c320beb591cc62f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FsumLeOf.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FsumLeOf.lean#L50-L56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumLeOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)

theorem P2M_RH_ReciprocityTheory_ChartRestriction_G_T0_Data_wx_mem_c320beb591cc62f2 (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«Data».«wx_mem» := P2M_RH_ReciprocityTheory_ChartRestriction_G_T0_Data_wx_mem_c320beb591cc62f2
