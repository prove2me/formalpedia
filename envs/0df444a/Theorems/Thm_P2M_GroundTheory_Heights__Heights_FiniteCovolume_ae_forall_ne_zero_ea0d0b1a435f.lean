-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ae_forall_ne_zero_ea0d0b1a435f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_ae_forall_ne_zero_ea0d0b1a435f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:37:33.245458+00:00
-- url     : https://prove2.me/theorems/2b3161dc-c70c-466f-ad92-8aee4fc97a25
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume ae forall ne zero ea0d0b1a435f: P2 M Ground Theory Heights  Heights Finite Covolume ae forall ne zero ea0d0b1a435f
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume ae forall ne zero ea0d0b1a435f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume ae forall ne zero ea0d0b1a435f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnfoldingTorus.lean#L62-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHaarParabolicCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingTorus
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
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_ae_forall_ne_zero_ea0d0b1a435f (κ : Type*) [Fintype κ] : ∀ᵐ b : κ → ℂ, ∀ w, b w ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«ae_forall_ne_zero» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_ae_forall_ne_zero_ea0d0b1a435f
