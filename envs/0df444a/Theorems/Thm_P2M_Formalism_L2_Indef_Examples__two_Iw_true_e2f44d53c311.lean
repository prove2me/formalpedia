-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__two_Iw_true_e2f44d53c311
-- name    : P2M_Formalism_L2_Indef_Examples__two_Iw_true_e2f44d53c311
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:06:25.320096+00:00
-- url     : https://prove2.me/theorems/1b12eb42-b2fe-593c-9c6c-27c1b4e14146
-- title:
--   P2 M Formalism L2 Indef Examples  two Iw true e2f44d53c311: P2 M Formalism L2 Indef Examples  two Iw true e2f44d53c311
-- statement:
--   The P2 M Formalism L2 Indef Examples  two Iw true e2f44d53c311 construction uses the P2 M Formalism L2 Indef Examples  two Iw true e2f44d53c311 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L713-L741
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L713-L741

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

theorem P2M_Formalism_L2_Indef_Examples__two_Iw_true_e2f44d53c311 {K : Type} [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : K) (kap l : InfinitePlace K → ℝ) (ha : a ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) : (two.dat K v0 S a kap l).Iw () true w = vw w a := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«two».«Iw_true» := P2M_Formalism_L2_Indef_Examples__two_Iw_true_e2f44d53c311
