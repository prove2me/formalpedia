-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentModulus_proof_b67cee2dd98a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentModulus_proof_b67cee2dd98a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:13:21.772751+00:00
-- url     : https://prove2.me/theorems/50d8a453-373b-5909-bf02-a7358d963e29
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Modulus proof b67cee2dd98a: P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Modulus proof b67cee2dd98a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Modulus proof b67cee2dd98a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Modulus proof b67cee2dd98a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulus.lean#L111-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulus.lean#L111-L164

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHomeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramAtData_proof_6f69e474274d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377

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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentModulus_proof_b67cee2dd98a (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentModulus.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipotentModulus».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentModulus_proof_b67cee2dd98a
