-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___127afe6e25e5
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___127afe6e25e5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:15.152003+00:00
-- url     : https://prove2.me/theorems/5c556026-d501-4863-9473-9798b9930622
-- title:
--   P2 M Positivity Theory Rg Sw LVs mul cm   127afe6e25e5: P2 M Positivity Theory Rg Sw LVs mul cm   127afe6e25e5
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs mul cm   127afe6e25e5 construction uses the P2 M Positivity Theory Rg Sw LVs mul cm   127afe6e25e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L40-L42

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___127afe6e25e5 (x : M2 n) : (x * Cm n).toBlocks₂₂ = u2 x := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«mul_cm₂₂» := P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___127afe6e25e5
