-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_archEmbed_mul_8e0f0497cff9
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_archEmbed_mul_8e0f0497cff9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:45:05.166879+00:00
-- url     : https://prove2.me/theorems/6ceeb46d-f8d4-5db9-b4f2-136ecca92435
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume inv Apply arch Embed mul 8e0f0497cff9: P2 M Ground Theory Heights  Heights Finite Covolume inv Apply arch Embed mul 8e0f0497cff9
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume inv Apply arch Embed mul 8e0f0497cff9 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume inv Apply arch Embed mul 8e0f0497cff9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMahlerCompactness.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMahlerCompactness.lean#L36-L42

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_archEmbed_mul_8e0f0497cff9 (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (g : archUnitary h v) (x : W) :
    invApply (archEmbed h v γ * g) (vecAt v ((γ : W ≃ₗ[E] W) x)) = invApply g (vecAt v x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«invApply_archEmbed_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_archEmbed_mul_8e0f0497cff9
