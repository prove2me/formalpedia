-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_mem_bdry_of_subsingleton_9fd4ef684c7c
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_mem_bdry_of_subsingleton_9fd4ef684c7c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:28:55.567307+00:00
-- url     : https://prove2.me/theorems/2f6278a9-1700-5b8f-985e-7c9f46ef39e4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Surjective Closed mem bdry of subsingleton 9fd4ef684c7c: P2 M Ground Theory Heights  Heights Kleiman Surjective Closed mem bdry of subsingleton 9fd4ef684c7c
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Surjective Closed mem bdry of subsingleton 9fd4ef684c7c construction uses the P2 M Ground Theory Heights  Heights Kleiman Surjective Closed mem bdry of subsingleton 9fd4ef684c7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L185-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L185-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_mem_bdry_of_subsingleton_9fd4ef684c7c {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
    {G : Cell U → Type w} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
    {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {i : ℕ} (h : Subsingleton (Cech.H G ρ i))
    (z : Cech.Cochain G i) (hz : z ∈ LinearMap.ker (Cech.d G ρ i)) : z ∈ Cech.bdry G ρ i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SurjectiveClosed».«mem_bdry_of_subsingleton» := P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_mem_bdry_of_subsingleton_9fd4ef684c7c
