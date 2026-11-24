-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_yRoot_eq_blockEmb_3d7bdf650708
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_yRoot_eq_blockEmb_3d7bdf650708
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:42.52577+00:00
-- url     : https://prove2.me/theorems/a951890f-20ed-4cfd-b02f-347d5b3f2690
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top y Root eq block Emb 3d7bdf650708: P2 M Ground Theory Heights  Heights Rest Terms Top y Root eq block Emb 3d7bdf650708
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top y Root eq block Emb 3d7bdf650708 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top y Root eq block Emb 3d7bdf650708 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L120-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_yRoot_eq_blockEmb_3d7bdf650708 (f r a : ℕ) (c : SmallBlock) (σ : Fin f) (i : Fin r) :
    yRoot f r a c σ i = blockEmb f (r + a) σ (yRoot 1 r a c 0 i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«yRoot_eq_blockEmb» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_yRoot_eq_blockEmb_3d7bdf650708
