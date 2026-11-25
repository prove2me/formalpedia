-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantExists_proof_4b92f33fe38c
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantExists_proof_4b92f33fe38c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:40:29.539177+00:00
-- url     : https://prove2.me/theorems/c314606e-4e18-53fb-a168-e609c7747816
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Exists proof 4b92f33fe38c: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Exists proof 4b92f33fe38c
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Exists proof 4b92f33fe38c construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Exists proof 4b92f33fe38c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantExists.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantExists.lean#L64-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantExists
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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantExists_proof_4b92f33fe38c (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : GramAtData.Statement h v) : MajorantExists.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantExists».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantExists_proof_4b92f33fe38c
