-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_baseChange_968fd6092864
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_baseChange_968fd6092864
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:17.344166+00:00
-- url     : https://prove2.me/theorems/f14e558b-965c-48ec-a8d2-1c2a7776ca78
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det base Change 968fd6092864: P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det base Change 968fd6092864
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det base Change 968fd6092864 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det base Change 968fd6092864 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PBaseChange.lean#L27-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PBaseChange.lean#L27-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct ComplexAt GroundTheory.Heights₂.Heights
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_baseChange_968fd6092864 (h : HermitianMetric K E) (τ : L →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → E) :
    gramDet (h.baseChange L) τ (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) =
      gramDet h (τ.comp (algebraMap K L)) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«gramDet_baseChange» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_baseChange_968fd6092864
