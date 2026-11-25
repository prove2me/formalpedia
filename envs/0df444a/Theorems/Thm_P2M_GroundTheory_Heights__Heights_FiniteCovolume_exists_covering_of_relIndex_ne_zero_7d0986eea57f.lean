-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_covering_of_relIndex_ne_zero_7d0986eea57f
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_covering_of_relIndex_ne_zero_7d0986eea57f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:38:09.646842+00:00
-- url     : https://prove2.me/theorems/e934a5ef-ff12-453e-80f1-b68bd7fcc6a5
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume exists covering of rel Index ne zero 7d0986eea57f: P2 M Ground Theory Heights  Heights Finite Covolume exists covering of rel Index ne zero 7d0986ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume exists covering of rel Index ne zero 7d0986eea57f construction uses the P2 M Ground Theory Heights  Heights Finite Covolume exists covering of rel Index ne zero 7d0986eea57f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerCovolume.lean#L20-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerCovolume.lean#L20-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PWittPartner
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDiscreteFundamentalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerCovolume
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
open scoped ENNReal Pointwise
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_covering_of_relIndex_ne_zero_7d0986eea57f {G K : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] [Group K] (μ : Measure G) [μ.IsMulLeftInvariant] (f : K →* G)
    (A B : Subgroup K) (hidx : A.relIndex B ≠ 0) (FD : Set G)
    (hFD : IsFundamentalDomain (B.map f) FD μ) (hfin : μ FD < ⊤) :
    ∃ T : Set G, MeasurableSet T ∧ μ T < ⊤ ∧ ∀ l, ∃ a ∈ A, f a * l ∈ T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«exists_covering_of_relIndex_ne_zero» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_covering_of_relIndex_ne_zero_7d0986eea57f
