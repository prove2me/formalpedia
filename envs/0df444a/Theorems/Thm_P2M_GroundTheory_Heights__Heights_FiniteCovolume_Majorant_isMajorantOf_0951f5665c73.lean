-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_Majorant_isMajorantOf_0951f5665c73
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_Majorant_isMajorantOf_0951f5665c73
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:31.112719+00:00
-- url     : https://prove2.me/theorems/ef9b19de-3ac1-5e8a-b82c-5761c818a443
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant is Majorant Of 0951f5665c73: P2 M Ground Theory Heights  Heights Finite Covolume Majorant is Majorant Of 0951f5665c73
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant is Majorant Of 0951f5665c73 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant is Majorant Of 0951f5665c73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenCauchySchwarz.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenCauchySchwarz.lean#L56-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLenCauchySchwarz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLenSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLenCauchySchwarz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_Majorant_isMajorantOf_0951f5665c73 {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (w : InfinitePlace E) : IsMajorantOf (gramAt h v w) (M.P w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«Majorant».«isMajorantOf» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_Majorant_isMajorantOf_0951f5665c73
