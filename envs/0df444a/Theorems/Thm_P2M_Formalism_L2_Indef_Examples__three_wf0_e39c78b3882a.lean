-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__three_wf0_e39c78b3882a
-- name    : P2M_Formalism_L2_Indef_Examples__three_wf0_e39c78b3882a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:57.525293+00:00
-- url     : https://prove2.me/theorems/124be103-0cc4-4326-86ba-fe518ce07f9e
-- title:
--   P2 M Formalism L2 Indef Examples  three wf0 e39c78b3882a: P2 M Formalism L2 Indef Examples  three wf0 e39c78b3882a
-- statement:
--   The P2 M Formalism L2 Indef Examples  three wf0 e39c78b3882a construction uses the P2 M Formalism L2 Indef Examples  three wf0 e39c78b3882a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L142-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L142-L157

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
open Formalism.L2.Indef.Examples₂.three
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K) (kap : ℝ)
  (l : Fin 2 → Fin 2 → ℝ)

theorem P2M_Formalism_L2_Indef_Examples__three_wf0_e39c78b3882a (hv0 : IsConjAt v0) : (df0 K v0).WF := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«three».«wf0» := P2M_Formalism_L2_Indef_Examples__three_wf0_e39c78b3882a
