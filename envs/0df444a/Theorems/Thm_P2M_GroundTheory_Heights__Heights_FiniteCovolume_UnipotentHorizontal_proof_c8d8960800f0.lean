-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentHorizontal_proof_c8d8960800f0
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentHorizontal_proof_c8d8960800f0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:13:55.824118+00:00
-- url     : https://prove2.me/theorems/6bf64e2f-7b6e-5d20-99b2-c56d105df7d2
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Horizontal proof c8d8960800f0: P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Horizontal proof c8d8960800f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Horizontal proof c8d8960800f0 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Horizontal proof c8d8960800f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentHorizontal.lean#L31-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentHorizontal.lean#L31-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipRadicalOfRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementArchCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMahlerCompactness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentHorizontal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchInvariant_proof_c3cce6e49c61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramAtData_proof_6f69e474274d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MahlerCompactness_proof_5174a6040fc4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentHorizontal_proof_c8d8960800f0 (h : HermitianForm F E W) (v : Basis ι E W)
    (h0 : RationalUnipotent.Statement h) (h4 : UnipRadicalOfRational.Statement h v)
    (h5 : ComplementArchCocompact.Statement h v) : UnipotentHorizontal.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipotentHorizontal».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentHorizontal_proof_c8d8960800f0
