-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_swap_62d69dcf7b6b
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_swap_62d69dcf7b6b
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:54.358587+00:00
-- url     : https://prove2.me/theorems/23a15675-a651-4115-830e-68f98d51b05e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central pair swap 62d69dcf7b6b: P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central pair swap 62d69dcf7b6b
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central pair swap 62d69dcf7b6b construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central pair swap 62d69dcf7b6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCentral.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCentral.lean#L35-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCentral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipRadicalOfRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCentral
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
attribute [local instance] archMulAction
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnipotentCentral
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_swap_62d69dcf7b6b {G : Matrix ι ι ℂ} (hG : G.IsHermitian) (a b : ι → ℂ) :
    star b ⬝ᵥ (G *ᵥ a) = star (star a ⬝ᵥ (G *ᵥ b)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipotentCentral».«pair_swap» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_swap_62d69dcf7b6b
