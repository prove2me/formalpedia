-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inv_eq_of_inG__f8fdb4
-- name    : PositivityTheory.Rg.Sw.LVs.inv_eq_of_inG
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:22.504422+00:00
-- url     : https://prove2.me/theorems/f8fdb416-959d-4f91-95ae-150e0231071c
-- title:
--   LVs: inv eq of in G
-- statement:
--   The LVs construction uses the inv eq of in G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulConjTransposeEq.lean#L68-L72

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

theorem PositivityTheory.Rg.Sw.LVs.inv_eq_of_inG {g : M2 n} (hg : InG g) : g⁻¹ = -(JJ n) * gᴴ * JJ n := by sorry
