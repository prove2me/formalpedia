-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_embOn_single_pf
-- name    : PositivityTheory.Rg.Sw.HSt.embOn_single_pf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:56.695215+00:00
-- url     : https://prove2.me/theorems/730b4ba4-5169-5088-aabd-7f5548be2c99
-- title:
--   HSt: emb On single pf
-- statement:
--   The HSt construction uses the emb On single pf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/DerivProdRangeSubMulProdNeZero.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/DerivProdRangeSubMulProdNeZero.lean#L14-L25

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_DerivProdRangeSubMulProdNeZero
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.HSt.embOn_single_pf (s : Finset (Fin n)) (a b : s) :
    embOn s (Matrix.single a b (1 : ℂ)) = Matrix.single (a : Fin n) (b : Fin n) 1 := by sorry
