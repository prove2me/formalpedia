-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__one_quot_de26657ef017
-- name    : P2M_Formalism_L2_Indef_Examples__one_quot_de26657ef017
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:13:16.21354+00:00
-- url     : https://prove2.me/theorems/48776119-3767-4876-bd71-dc7d96cf9bbd
-- title:
--   P2 M Formalism L2 Indef Examples  one quot de26657ef017: P2 M Formalism L2 Indef Examples  one quot de26657ef017
-- statement:
--   The P2 M Formalism L2 Indef Examples  one quot de26657ef017 construction uses the P2 M Formalism L2 Indef Examples  one quot de26657ef017 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L90-L92

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
variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_L2_Indef_Examples__one_quot_de26657ef017 (n : ℕ) : IsQuotMetric (1 : Matrix (Fin n) (Fin n) K) 1 (fr K n) := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«one_quot» := P2M_Formalism_L2_Indef_Examples__one_quot_de26657ef017
