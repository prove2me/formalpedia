-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___89a26790be15
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___89a26790be15
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:20.831824+00:00
-- url     : https://prove2.me/theorems/96eea51d-540b-4a7c-ad7b-286047cb6b68
-- title:
--   P2 M Positivity Theory Rg Sw LVs mul cm   89a26790be15: P2 M Positivity Theory Rg Sw LVs mul cm   89a26790be15
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs mul cm   89a26790be15 construction uses the P2 M Positivity Theory Rg Sw LVs mul cm   89a26790be15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L36-L38

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___89a26790be15 (x : M2 n) : (x * Cm n).toBlocks₂₁ = u1 x := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«mul_cm₂₁» := P2M_PositivityTheory_Rg_Sw_LVs_mul_cm___89a26790be15
