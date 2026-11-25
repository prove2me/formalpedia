-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_trace_mul_dual
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.trace_mul_dual
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:14:14.536643+00:00
-- url     : https://prove2.me/theorems/3f412dda-5e65-4af6-a39a-5d63e894c1fe
-- title:
--   Eig A: trace mul dual
-- statement:
--   The Eig A construction uses the trace mul dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/IdemDataBasis.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/IdemDataBasis.lean#L48-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBIdemDen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.trace_mul_dual {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (k i : ι) :
    Algebra.trace ℚ E (b k * TB.trDual b i) = if k = i then 1 else 0 := by sorry
