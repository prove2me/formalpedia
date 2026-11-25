-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_tsum_orbit_eq_tsum_quotient_4af71a9ca89b
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_tsum_orbit_eq_tsum_quotient_4af71a9ca89b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:42.00862+00:00
-- url     : https://prove2.me/theorems/6a61511b-dcff-42d1-aad0-b66ca3d2dd07
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume tsum orbit eq tsum quotient 4af71a9ca89b: P2 M Ground Theory Heights  Heights Finite Covolume tsum orbit eq tsum quotient 4af71a9ca89b
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume tsum orbit eq tsum quotient 4af71a9ca89b construction uses the P2 M Ground Theory Heights  Heights Finite Covolume tsum orbit eq tsum quotient 4af71a9ca89b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_tsum_orbit_eq_tsum_quotient_4af71a9ca89b {G X : Type*} [Group G] [MulAction G X] (b : X) (o : Set X)
    (ho : MulAction.orbit G b = o) (K : Subgroup G) (hK : MulAction.stabilizer G b = K)
    (f : X → ℝ≥0∞) : ∑' p : o, f p = ∑' q : G ⧸ K, f ((Quotient.out q : G) • b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«tsum_orbit_eq_tsum_quotient» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_tsum_orbit_eq_tsum_quotient_4af71a9ca89b
