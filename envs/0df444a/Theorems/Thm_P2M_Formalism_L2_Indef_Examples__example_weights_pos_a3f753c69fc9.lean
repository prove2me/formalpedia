-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__example_weights_pos_a3f753c69fc9
-- name    : P2M_Formalism_L2_Indef_Examples__example_weights_pos_a3f753c69fc9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:07:56.102853+00:00
-- url     : https://prove2.me/theorems/364e5f7e-2a9e-442b-a91e-9a8c6a1f5c05
-- title:
--   P2 M Formalism L2 Indef Examples  example weights pos a3f753c69fc9: P2 M Formalism L2 Indef Examples  example weights pos a3f753c69fc9
-- statement:
--   The P2 M Formalism L2 Indef Examples  example weights pos a3f753c69fc9 construction uses the P2 M Formalism L2 Indef Examples  example weights pos a3f753c69fc9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L344-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L344-L344

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_QuadraticExampleRankThreePackage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Examples₂
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

theorem P2M_Formalism_L2_Indef_Examples__example_weights_pos_a3f753c69fc9 (j p : Fin 2) : 0 < l4 j p := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«example_weights_pos» := P2M_Formalism_L2_Indef_Examples__example_weights_pos_a3f753c69fc9
