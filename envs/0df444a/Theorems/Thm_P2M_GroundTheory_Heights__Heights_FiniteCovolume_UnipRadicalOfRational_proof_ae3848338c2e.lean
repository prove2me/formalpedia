-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipRadicalOfRational_proof_ae3848338c2e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipRadicalOfRational_proof_ae3848338c2e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:27:52.706477+00:00
-- url     : https://prove2.me/theorems/5dee6977-9a77-4119-89f9-bd642b20559b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unip Radical Of Rational proof ae3848338c2e: P2 M Ground Theory Heights  Heights Finite Covolume Unip Radical Of Rational proof ae3848338c2e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unip Radical Of Rational proof ae3848338c2e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unip Radical Of Rational proof ae3848338c2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipRadicalOfRational.lean#L16-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipRadicalOfRational.lean#L16-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipRadicalOfRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipRadicalOfRational
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3

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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipRadicalOfRational_proof_ae3848338c2e (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipRadicalOfRational.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipRadicalOfRational».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipRadicalOfRational_proof_ae3848338c2e
