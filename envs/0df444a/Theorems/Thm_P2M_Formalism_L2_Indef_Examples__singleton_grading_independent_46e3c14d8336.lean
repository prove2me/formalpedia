-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__singleton_grading_independent_46e3c14d8336
-- name    : P2M_Formalism_L2_Indef_Examples__singleton_grading_independent_46e3c14d8336
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:08:02.34518+00:00
-- url     : https://prove2.me/theorems/2d70a440-e22d-4134-8524-258663434bf7
-- title:
--   P2 M Formalism L2 Indef Examples  singleton grading independent 46e3c14d8336: P2 M Formalism L2 Indef Examples  singleton grading independent 46e3c14d8336
-- statement:
--   The P2 M Formalism L2 Indef Examples  singleton grading independent 46e3c14d8336 construction uses the P2 M Formalism L2 Indef Examples  singleton grading independent 46e3c14d8336 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L67-L69

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_L2_Indef_Examples__singleton_grading_independent_46e3c14d8336 (V : Type) [AddCommGroup V] [Module K V] : iSupIndep (only0 (K := K) V) := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«singleton_grading_independent» := P2M_Formalism_L2_Indef_Examples__singleton_grading_independent_46e3c14d8336
