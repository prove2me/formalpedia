-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_top_8f7be36c5b52
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_top_8f7be36c5b52
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:44:17.406497+00:00
-- url     : https://prove2.me/theorems/f6b184d4-87df-4125-b483-efee1dad4d4d
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg sub top 8f7be36c5b52: P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg sub top 8f7be36c5b52
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg sub top 8f7be36c5b52 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas Chain Sum deg sub top 8f7be36c5b52 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PChainSum.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PChainSum.lean#L38-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PChainSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
open GroundTheory.Heights₂.Heights.LatticeLemmas.ChainSum

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_top_8f7be36c5b52 {K : Type u} [Field K] [NumberField K] (M : HermitianBundle.{v} K) :
    (M.sub ⊤).deg = M.deg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«ChainSum».«deg_sub_top» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_ChainSum_deg_sub_top_8f7be36c5b52
