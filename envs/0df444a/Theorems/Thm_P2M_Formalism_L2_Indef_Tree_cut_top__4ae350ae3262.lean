-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Tree_cut_top__4ae350ae3262
-- name    : P2M_Formalism_L2_Indef_Tree_cut_top__4ae350ae3262
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:44.193159+00:00
-- url     : https://prove2.me/theorems/5f1b94a7-267d-514f-915e-479bd51679aa
-- title:
--   P2 M Formalism L2 Indef Tree cut top  4ae350ae3262: P2 M Formalism L2 Indef Tree cut top  4ae350ae3262
-- statement:
--   The P2 M Formalism L2 Indef Tree cut top  4ae350ae3262 construction uses the P2 M Formalism L2 Indef Tree cut top  4ae350ae3262 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L993-L995
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L993-L995

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
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
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (K)

theorem P2M_Formalism_L2_Indef_Tree_cut_top__4ae350ae3262 {n : ℕ} (A : Submodule (𝓞 K) (Fin n → K)) : cut (⊤ : Submodule K (Fin n → K)) A = A := by sorry

alias «Formalism».«L2».«Indef».«Tree».«cut_top'» := P2M_Formalism_L2_Indef_Tree_cut_top__4ae350ae3262
