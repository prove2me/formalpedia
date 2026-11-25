-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__scal_comap_6bb2b35a3d73
-- name    : P2M_Formalism_L2_Indef_Examples__scal_comap_6bb2b35a3d73
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:46.540799+00:00
-- url     : https://prove2.me/theorems/58171bbd-7d7e-4e8d-8dc8-407f2a209042
-- title:
--   P2 M Formalism L2 Indef Examples  scal comap 6bb2b35a3d73: P2 M Formalism L2 Indef Examples  scal comap 6bb2b35a3d73
-- statement:
--   The P2 M Formalism L2 Indef Examples  scal comap 6bb2b35a3d73 construction uses the P2 M Formalism L2 Indef Examples  scal comap 6bb2b35a3d73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L195-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L195-L204

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
variable {K}

theorem P2M_Formalism_L2_Indef_Examples__scal_comap_6bb2b35a3d73 {d d' : ℕ} {XS : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ}
    {XT : InfinitePlace K → Matrix (Fin d') (Fin d') ℂ} {v : InfinitePlace K} {φ : Matrix (Fin d') (Fin d) K}
    {A : Submodule K (Fin d → K)} {E : Submodule K (Fin d' → K)} {s : ℝ} (hφ : Function.Bijective φ.mulVec)
    (hmap : A.map φ.mulVecLin = E) (h : IsScalarOn XS XT v φ A s) :
    IsScalarOn XS XT v φ (E.comap φ.mulVecLin) s := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«scal_comap» := P2M_Formalism_L2_Indef_Examples__scal_comap_6bb2b35a3d73
