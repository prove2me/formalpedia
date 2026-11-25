-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_HarishChandra_conjU___543297810786
-- name    : P2M_GroundTheory_Automorphic_HarishChandra_conjU___543297810786
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:54:51.253028+00:00
-- url     : https://prove2.me/theorems/dbc87b4e-c648-4c93-89fd-c8c5994e1f03
-- title:
--   P2 M Ground Theory Automorphic Harish Chandra conj U   543297810786: P2 M Ground Theory Automorphic Harish Chandra conj U   543297810786
-- statement:
--   The P2 M Ground Theory Automorphic Harish Chandra conj U   543297810786 construction uses the P2 M Ground Theory Automorphic Harish Chandra conj U   543297810786 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Consequences.lean#L40-L42

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Consequences
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}

theorem P2M_GroundTheory_Automorphic_HarishChandra_conjU___543297810786 (g : (gl n)ˣ) (X : gl n) :
    conjU g (UniversalEnvelopingAlgebra.ι ℂ X) = UniversalEnvelopingAlgebra.ι ℂ ((g : gl n) * X * ↑g⁻¹) := by sorry

alias «GroundTheory».«Automorphic».«HarishChandra».«conjU_ι» := P2M_GroundTheory_Automorphic_HarishChandra_conjU___543297810786
