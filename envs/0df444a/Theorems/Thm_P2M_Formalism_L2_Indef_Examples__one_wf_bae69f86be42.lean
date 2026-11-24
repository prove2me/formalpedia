-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__one_wf_bae69f86be42
-- name    : P2M_Formalism_L2_Indef_Examples__one_wf_bae69f86be42
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:13:14.9874+00:00
-- url     : https://prove2.me/theorems/58e9e5cd-aae3-4c71-85c4-0b42ccf91863
-- title:
--   P2 M Formalism L2 Indef Examples  one wf bae69f86be42: P2 M Formalism L2 Indef Examples  one wf bae69f86be42
-- statement:
--   The P2 M Formalism L2 Indef Examples  one wf bae69f86be42 construction uses the P2 M Formalism L2 Indef Examples  one wf bae69f86be42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L302-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L302-L317

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
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
open Formalism.L2.Indef.Examples₂.one
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)

theorem P2M_Formalism_L2_Indef_Examples__one_wf_bae69f86be42 (hv0 : IsConjAt v0) : (df K v0).WF := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«one».«wf» := P2M_Formalism_L2_Indef_Examples__one_wf_bae69f86be42
