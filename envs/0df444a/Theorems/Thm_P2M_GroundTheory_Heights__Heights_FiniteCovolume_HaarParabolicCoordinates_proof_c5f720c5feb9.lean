-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HaarParabolicCoordinates_proof_c5f720c5feb9
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_HaarParabolicCoordinates_proof_c5f720c5feb9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:28:46.415297+00:00
-- url     : https://prove2.me/theorems/b6873ddf-9d02-4f1d-be95-799b392214b9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Haar Parabolic Coordinates proof c5f720c5feb9: P2 M Ground Theory Heights  Heights Finite Covolume Haar Parabolic Coordinates proof c5f720c5feb9
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Haar Parabolic Coordinates proof c5f720c5feb9 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Haar Parabolic Coordinates proof c5f720c5feb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHaarParabolicCoordinates.lean#L21-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHaarParabolicCoordinates.lean#L21-L60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHaarParabolicCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineStabHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsArchUnimodular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsMajorantStabCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHaarParabolicCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_HaarParabolicCoordinates_proof_c5f720c5feb9 (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ParabolicDecomposition.Statement h v) (h₂ : ArchUnimodular.Statement h v)
    (h₃ : MajorantStabCompact.Statement h v) (h₄ : LineStabHaar.Statement h v) :
    HaarParabolicCoordinates.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«HaarParabolicCoordinates».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_HaarParabolicCoordinates_proof_c5f720c5feb9
