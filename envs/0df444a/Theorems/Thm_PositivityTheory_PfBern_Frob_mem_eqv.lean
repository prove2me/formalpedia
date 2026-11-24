-- Prove2me | Theorems.Thm_PositivityTheory_PfBern_Frob_mem_eqv
-- name    : PositivityTheory.PfBern.Frob.mem_eqv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:52.6898+00:00
-- url     : https://prove2.me/theorems/beadf9e5-bd5f-4d28-937e-e2e7339ea483
-- title:
--   Frob: mem eqv
-- statement:
--   The Frob construction uses the mem eqv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/PullHomeoApply.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/BernsteinUnitaryProducts/BernsteinTheoremA/FrobeniusReciprocity/PullHomeoApply.lean#L57-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_PullHomeoApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [ContinuousConstSMul G X]

theorem PositivityTheory.PfBern.Frob.mem_eqv {χ : G →* ℂˣ} {D : Distr X} :
    D ∈ eqv X χ ↔ ∀ (g : G) (f : SB X), D (transl g f) = (χ g : ℂ) * D f := by sorry
