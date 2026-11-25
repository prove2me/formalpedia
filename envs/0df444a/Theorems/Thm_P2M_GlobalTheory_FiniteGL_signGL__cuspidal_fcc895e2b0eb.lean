-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FiniteGL_signGL__cuspidal_fcc895e2b0eb
-- name    : P2M_GlobalTheory_FiniteGL_signGL__cuspidal_fcc895e2b0eb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T18:03:28.663946+00:00
-- url     : https://prove2.me/theorems/177ba5ec-e0f3-5187-af0f-f0340cf89537
-- title:
--   P2 M Global Theory Finite GL sign GL  cuspidal fcc895e2b0eb: P2 M Global Theory Finite GL sign GL  cuspidal fcc895e2b0eb
-- statement:
--   The P2 M Global Theory Finite GL sign GL  cuspidal fcc895e2b0eb construction uses the P2 M Global Theory Finite GL sign GL  cuspidal fcc895e2b0eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L192-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/BlockTriangularOfSubOne.lean#L192-L205

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.EigenvalueLevelCeiling Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.FiniteGL

theorem P2M_GlobalTheory_FiniteGL_signGL__cuspidal_fcc895e2b0eb : (lineRep signGL₂).IsIrreducible ∧ IsCuspidal (lineRep signGL₂) := by sorry

alias «GlobalTheory».«FiniteGL».«signGL₂_cuspidal» := P2M_GlobalTheory_FiniteGL_signGL__cuspidal_fcc895e2b0eb
