-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_integrable_log_norm_sub_log_norm
-- name    : ReciprocityTheory.ChartRestriction.G.T0.Data.integrable_log_norm_sub_log_norm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:36:48.941328+00:00
-- url     : https://prove2.me/theorems/d5b0bafd-f9b7-44d5-8f7f-173bbb8db712
-- title:
--   Data: integrable log norm sub log norm
-- statement:
--   The Data construction uses the integrable log norm sub log norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/EvTEqBlockPointOfMh.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/EvTEqBlockPointOfMh.lean#L80-L85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvTEqBlockPointOfMh
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

theorem ReciprocityTheory.ChartRestriction.G.T0.Data.integrable_log_norm_sub_log_norm (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    MeasureTheory.Integrable (fun z => Real.log ‖d.evT sg 0 (d.tOf z) a‖ -
      Real.log ‖d.evT sg 0 (d.tOf z) b‖) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by sorry
