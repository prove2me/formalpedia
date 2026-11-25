-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_map_1efb3bf7d4ae
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_map_1efb3bf7d4ae
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:06:56.137887+00:00
-- url     : https://prove2.me/theorems/1f8645fc-cfe2-5ddc-ae7d-743bc96a2d2f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central pair map 1efb3bf7d4ae: P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central pair map 1efb3bf7d4ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central pair map 1efb3bf7d4ae construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Unipotent Central pair map 1efb3bf7d4ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCentral.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentCentral.lean#L26-L31

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_map_1efb3bf7d4ae {G g : Matrix ι ι ℂ} (hg : (g.map (starRingEnd ℂ))ᵀ * G * g = G)
    (a b : ι → ℂ) : star (g *ᵥ a) ⬝ᵥ (G *ᵥ (g *ᵥ b)) = star a ⬝ᵥ (G *ᵥ b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«UnipotentCentral».«pair_map» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCentral_pair_map_1efb3bf7d4ae
