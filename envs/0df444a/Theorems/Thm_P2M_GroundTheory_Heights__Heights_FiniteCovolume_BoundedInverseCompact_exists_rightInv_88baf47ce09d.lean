-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_exists_rightInv_88baf47ce09d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_exists_rightInv_88baf47ce09d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:22.048787+00:00
-- url     : https://prove2.me/theorems/da130095-124b-48cf-b37e-57e1ea94f55a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact exists right Inv 88baf47ce09d: P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact exists right Inv
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact exists right Inv 88baf47ce09d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact exists right Inv 88baf47ce09d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedInverseCompact.lean#L70-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedInverseCompact.lean#L70-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedInverseCompact
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
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.BoundedInverseCompact
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [IsTotallyComplex E] [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_exists_rightInv_88baf47ce09d (v : Basis ι E W) {n : ℕ} {e : Fin n → W}
    (he : Submodule.span E (Set.range e) = ⊤) :
    ∃ c : ι → Fin n → E, ∀ w : InfinitePlace E,
      (Matrix.of fun k a => vecAt v (e a) w k) * (Matrix.of fun a i => w.embedding (c i a)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«BoundedInverseCompact».«exists_rightInv» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_exists_rightInv_88baf47ce09d
