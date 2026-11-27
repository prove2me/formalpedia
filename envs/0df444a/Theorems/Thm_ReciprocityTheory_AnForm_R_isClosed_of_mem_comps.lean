-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isClosed_of_mem_comps
-- name    : ReciprocityTheory.AnForm.R.isClosed_of_mem_comps
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:32.050932+00:00
-- url     : https://prove2.me/theorems/8e514782-3c28-5f5a-a5e0-2b4350fb4fa9
-- title:
--   R: is Closed of mem comps
-- statement:
--   The R construction uses the is Closed of mem comps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L45-L49

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages
noncomputable section
variable {α : Type*} [TopologicalSpace α]

theorem ReciprocityTheory.AnForm.R.isClosed_of_mem_comps {T : Set α} (hT : IsClosed T) {C : Set α} (hC : C ∈ comps T) :
    IsClosed C := by sorry
