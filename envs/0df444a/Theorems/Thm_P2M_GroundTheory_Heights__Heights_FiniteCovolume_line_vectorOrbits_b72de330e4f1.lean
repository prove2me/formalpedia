-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_line_vectorOrbits_b72de330e4f1
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_line_vectorOrbits_b72de330e4f1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:46.025284+00:00
-- url     : https://prove2.me/theorems/350652e7-f217-41bf-b5ec-ce9ef312ae78
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume line vector Orbits b72de330e4f1: P2 M Ground Theory Heights  Heights Finite Covolume line vector Orbits b72de330e4f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume line vector Orbits b72de330e4f1 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume line vector Orbits b72de330e4f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L58-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PVectorOrbitsFinite.lean#L58-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceUnitsFiniteIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_line_vectorOrbits_b72de330e4f1 (h : HermitianForm F E W) (h₂ : IsotropicScaling.Statement h)
    (h₃ : BoundedIndexSubgroupsFinite.Statement W) (h₅ : LineIndexNeZero.Statement E W)
    {D : ℕ} {La : AddSubgroup W} {VV : Set W} (hLa : IsDIntegral h D La) (hsub : VV ⊆ La)
    (hiso : ∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) {C : ℕ} (hC : ∀ x ∈ VV, lineIndex E La x ≤ C)
    {v₀ : W} (hv₀ : v₀ ∈ VV) :
    ∃ S : Finset W, (S : Set W) ⊆ VV ∧ ∀ x ∈ VV, x ∈ Submodule.span E {v₀} →
      ∃ y ∈ S, ∃ γ ∈ latticeStab h La, γ • y = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«line_vectorOrbits» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_line_vectorOrbits_b72de330e4f1
