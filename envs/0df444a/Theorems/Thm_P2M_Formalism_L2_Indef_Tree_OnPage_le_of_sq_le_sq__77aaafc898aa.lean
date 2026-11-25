-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Tree_OnPage_le_of_sq_le_sq__77aaafc898aa
-- name    : P2M_Formalism_L2_Indef_Tree_OnPage_le_of_sq_le_sq__77aaafc898aa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:33:09.013733+00:00
-- url     : https://prove2.me/theorems/45f215cd-e121-51cd-ba51-ca4887a463ea
-- title:
--   P2 M Formalism L2 Indef Tree On Page le of sq le sq  77aaafc898aa: P2 M Formalism L2 Indef Tree On Page le of sq le sq  77aaafc898aa
-- statement:
--   The P2 M Formalism L2 Indef Tree On Page le of sq le sq  77aaafc898aa construction uses the P2 M Formalism L2 Indef Tree On Page le of sq le sq  77aaafc898aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONPage.lean#L125-L129

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONPage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.L2.Indef.Tree.OnPage
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

theorem P2M_Formalism_L2_Indef_Tree_OnPage_le_of_sq_le_sq__77aaafc898aa (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by sorry

alias «Formalism».«L2».«Indef».«Tree».«OnPage».«le_of_sq_le_sq'» := P2M_Formalism_L2_Indef_Tree_OnPage_le_of_sq_le_sq__77aaafc898aa
