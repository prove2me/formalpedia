-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__two_wf_0e62dc323dfc
-- name    : P2M_Formalism_L2_Indef_Examples__two_wf_0e62dc323dfc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:46.887434+00:00
-- url     : https://prove2.me/theorems/d368287b-3340-42d7-bb80-2d434ac12b8c
-- title:
--   P2 M Formalism L2 Indef Examples  two wf 0e62dc323dfc: P2 M Formalism L2 Indef Examples  two wf 0e62dc323dfc
-- statement:
--   The P2 M Formalism L2 Indef Examples  two wf 0e62dc323dfc construction uses the P2 M Formalism L2 Indef Examples  two wf 0e62dc323dfc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L486-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L486-L501

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
open Formalism.L2.Indef.Examples₂.two
open scoped Classical
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
  (S : Finset (HeightOneSpectrum (𝓞 K))) (a : K) (kap l : InfinitePlace K → ℝ)

theorem P2M_Formalism_L2_Indef_Examples__two_wf_0e62dc323dfc (hv0 : IsConjAt v0) : (df K v0).WF := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«two».«wf» := P2M_Formalism_L2_Indef_Examples__two_wf_0e62dc323dfc
