-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Tree_map_id__e509ab30fe6d
-- name    : P2M_Formalism_L2_Indef_Tree_map_id__e509ab30fe6d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:05.602732+00:00
-- url     : https://prove2.me/theorems/1a8e0bdb-d2ac-5fe4-b3ed-a774a4ccf0e8
-- title:
--   P2 M Formalism L2 Indef Tree map id  e509ab30fe6d: P2 M Formalism L2 Indef Tree map id  e509ab30fe6d
-- statement:
--   The P2 M Formalism L2 Indef Tree map id  e509ab30fe6d construction uses the P2 M Formalism L2 Indef Tree map id  e509ab30fe6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L987-L991
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ExampleSatisfiesConditionsAtFive.lean#L987-L991

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

theorem P2M_Formalism_L2_Indef_Tree_map_id__e509ab30fe6d {n : ℕ} (A : Submodule (𝓞 K) (Fin n → K)) :
    A.map ((LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K)).restrictScalars (𝓞 K)) = A := by sorry

alias «Formalism».«L2».«Indef».«Tree».«map_id'» := P2M_Formalism_L2_Indef_Tree_map_id__e509ab30fe6d
