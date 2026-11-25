-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_gen_prime__368b34e1e491
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_gen_prime__368b34e1e491
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:53:23.755098+00:00
-- url     : https://prove2.me/theorems/f1079f2a-394b-4e7a-b1b6-b699061d15d1
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 Data gen prime  368b34e1e491: P2 M Reciprocity Theory Chart Restriction G T0 Data gen prime  368b34e1e491
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 Data gen prime  368b34e1e491 construction uses the P2 M Reciprocity Theory Chart Restriction G T0 Data gen prime  368b34e1e491 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UnitAtIntAt.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UnitAtIntAt.lean#L116-L117

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_gen_prime__368b34e1e491 {q : Ideal (KTp K d.D d.N)} (hq : q ∈ d.HtOne) : Prime (d.gen q) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«Data».«gen_prime'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_gen_prime__368b34e1e491
