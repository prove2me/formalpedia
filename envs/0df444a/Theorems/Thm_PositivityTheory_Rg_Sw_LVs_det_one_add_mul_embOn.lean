-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_one_add_mul_embOn
-- name    : PositivityTheory.Rg.Sw.LVs.det_one_add_mul_embOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:11.581989+00:00
-- url     : https://prove2.me/theorems/de51f991-41a6-44bd-9e78-103f2c7bac39
-- title:
--   LVs: det one add mul emb On
-- statement:
--   The LVs construction uses the det one add mul emb On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L103-L109

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

theorem PositivityTheory.Rg.Sw.LVs.det_one_add_mul_embOn (s : Finset (Fin n)) (M : Matrix (Fin n) (Fin n) ℂ) (T : Matrix s s ℂ) :
    (1 + M * embOn s T).det = (1 + subOn s M * T).det := by sorry
