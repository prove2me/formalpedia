-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MahlerCompactness_proof_5174a6040fc4
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MahlerCompactness_proof_5174a6040fc4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:29.563869+00:00
-- url     : https://prove2.me/theorems/430ffcc8-19b5-589d-8efe-6ed0f76b3ed9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Mahler Compactness proof 5174a6040fc4: P2 M Ground Theory Heights  Heights Finite Covolume Mahler Compactness proof 5174a6040fc4
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Mahler Compactness proof 5174a6040fc4 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Mahler Compactness proof 5174a6040fc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMahlerCompactness.lean#L44-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMahlerCompactness.lean#L44-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLenCauchySchwarz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StGramDetermines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMahlerCompactness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MahlerCompactness_proof_5174a6040fc4 (h : HermitianForm F E W) (v : Basis ι E W)
    (hB : BoundedGenerators.Statement h v) (hCS : LenCauchySchwarz.Statement h v)
    (hG : GramDetermines.Statement h) (hK : BoundedInverseCompact.Statement h v) :
    MahlerCompactness.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MahlerCompactness».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MahlerCompactness_proof_5174a6040fc4
