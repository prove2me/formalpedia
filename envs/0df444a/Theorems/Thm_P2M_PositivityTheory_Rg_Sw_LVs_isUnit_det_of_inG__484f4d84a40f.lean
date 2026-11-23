-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_inG__484f4d84a40f
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_inG__484f4d84a40f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:47.415849+00:00
-- url     : https://prove2.me/theorems/80d88e42-807b-4a6d-9b25-2f55b4e62ed6
-- title:
--   P2 M Positivity Theory Rg Sw LVs is Unit det of in G  484f4d84a40f: P2 M Positivity Theory Rg Sw LVs is Unit det of in G  484f4d84a40f
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs is Unit det of in G  484f4d84a40f construction uses the P2 M Positivity Theory Rg Sw LVs is Unit det of in G  484f4d84a40f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L20-L30

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSimpArgs false
open Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_inG__484f4d84a40f {g : M2 n} (hg : InG g) : IsUnit g.det := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«isUnit_det_of_inG'» := P2M_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_inG__484f4d84a40f
