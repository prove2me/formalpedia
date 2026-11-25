-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_mX_eq__121fdc765cb7
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_mX_eq__121fdc765cb7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:11:04.821389+00:00
-- url     : https://prove2.me/theorems/16c3bc11-ab1b-4001-9357-3191acc5c3f2
-- title:
--   P2 M Positivity Theory Rg Sw LVs m X eq  121fdc765cb7: P2 M Positivity Theory Rg Sw LVs m X eq  121fdc765cb7
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs m X eq  121fdc765cb7 construction uses the P2 M Positivity Theory Rg Sw LVs m X eq  121fdc765cb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L149-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L149-L150

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_PositivityTheory_Rg_Sw_LVs_mX_eq__121fdc765cb7 (Q R : Matrix (Fin n) (Fin n) ℂ) : mX 1 Q R 1 = 1 + Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹ := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«mX_eq'» := P2M_PositivityTheory_Rg_Sw_LVs_mX_eq__121fdc765cb7
