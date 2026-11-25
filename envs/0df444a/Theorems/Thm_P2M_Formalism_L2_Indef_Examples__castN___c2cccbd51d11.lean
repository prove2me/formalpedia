-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__castN___c2cccbd51d11
-- name    : P2M_Formalism_L2_Indef_Examples__castN___c2cccbd51d11
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:53.52781+00:00
-- url     : https://prove2.me/theorems/4faa1ccc-d61c-5fa3-9e25-232f31e48ae8
-- title:
--   P2 M Formalism L2 Indef Examples  cast N   c2cccbd51d11: P2 M Formalism L2 Indef Examples  cast N   c2cccbd51d11
-- statement:
--   The P2 M Formalism L2 Indef Examples  cast N   c2cccbd51d11 construction uses the P2 M Formalism L2 Indef Examples  cast N   c2cccbd51d11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L262-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L262-L265

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem P2M_Formalism_L2_Indef_Examples__castN___c2cccbd51d11 {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N N' : IndefNum Bs}
    (h : N = N') (P : IndefCore Df0 Df1 Dc Sp N) : (castN h P).base.μ = P.base.μ := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«castN_μ» := P2M_Formalism_L2_Indef_Examples__castN___c2cccbd51d11
