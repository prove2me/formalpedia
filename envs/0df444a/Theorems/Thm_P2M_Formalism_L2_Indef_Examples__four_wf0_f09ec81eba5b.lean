-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__four_wf0_f09ec81eba5b
-- name    : P2M_Formalism_L2_Indef_Examples__four_wf0_f09ec81eba5b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:07:13.221905+00:00
-- url     : https://prove2.me/theorems/6aa5cf41-15b6-47c1-b84f-9aa7dfb4f9c1
-- title:
--   P2 M Formalism L2 Indef Examples  four wf0 f09ec81eba5b: P2 M Formalism L2 Indef Examples  four wf0 f09ec81eba5b
-- statement:
--   The P2 M Formalism L2 Indef Examples  four wf0 f09ec81eba5b construction uses the P2 M Formalism L2 Indef Examples  four wf0 f09ec81eba5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L466-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean#L466-L481

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
open Formalism.L2.Indef.Examples₂.four
open scoped Classical
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
  (S : Finset (HeightOneSpectrum (𝓞 K))) (b : Fin 2 → Fin 2 → K) (kap : ℝ) (l : Fin 2 → Fin 2 → ℝ)

theorem P2M_Formalism_L2_Indef_Examples__four_wf0_f09ec81eba5b (hv0 : IsConjAt v0) : (df0 K v0).WF := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«four».«wf0» := P2M_Formalism_L2_Indef_Examples__four_wf0_f09ec81eba5b
