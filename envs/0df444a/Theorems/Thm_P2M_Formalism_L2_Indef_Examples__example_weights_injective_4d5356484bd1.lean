-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__example_weights_injective_4d5356484bd1
-- name    : P2M_Formalism_L2_Indef_Examples__example_weights_injective_4d5356484bd1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:12:00.344493+00:00
-- url     : https://prove2.me/theorems/99ea8315-c72e-5a32-8c9c-9fcf1d0d0ee3
-- title:
--   P2 M Formalism L2 Indef Examples  example weights injective 4d5356484bd1: P2 M Formalism L2 Indef Examples  example weights injective 4d5356484bd1
-- statement:
--   The P2 M Formalism L2 Indef Examples  example weights injective 4d5356484bd1 construction uses the P2 M Formalism L2 Indef Examples  example weights injective 4d5356484bd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L346-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L346-L348

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

theorem P2M_Formalism_L2_Indef_Examples__example_weights_injective_4d5356484bd1 : Function.Injective fun x : Fin 2 × Fin 2 => l4 x.1 x.2 := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«example_weights_injective» := P2M_Formalism_L2_Indef_Examples__example_weights_injective_4d5356484bd1
