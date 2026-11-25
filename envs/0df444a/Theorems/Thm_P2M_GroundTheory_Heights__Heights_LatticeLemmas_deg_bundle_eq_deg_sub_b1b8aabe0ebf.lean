-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_deg_bundle_eq_deg_sub_b1b8aabe0ebf
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_deg_bundle_eq_deg_sub_b1b8aabe0ebf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:12.039295+00:00
-- url     : https://prove2.me/theorems/018edf21-2cbc-5802-a5ef-748e399f50ae
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas deg bundle eq deg sub b1b8aabe0ebf: P2 M Ground Theory Heights  Heights Lattice Lemmas deg bundle eq deg sub b1b8aabe0ebf
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas deg bundle eq deg sub b1b8aabe0ebf construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas deg bundle eq deg sub b1b8aabe0ebf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalChange.lean#L51-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalChange
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
open NumberField IsDedekindDomain TensorProduct ComplexAt
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_deg_bundle_eq_deg_sub_b1b8aabe0ebf (Nm : HermitianNorms K V) (M L : FullLattice K V)
    (hLM : L.carrier ≤ M.carrier) :
    (Nm.bundle L).deg = ((Nm.bundle M).sub (L.carrier.comap M.carrier.subtype)).deg := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«deg_bundle_eq_deg_sub» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_deg_bundle_eq_deg_sub_b1b8aabe0ebf
