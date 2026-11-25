-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartGens_mem_8cd9915ac670
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartGens_mem_8cd9915ac670
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:58:48.084147+00:00
-- url     : https://prove2.me/theorems/b7f6240d-b70d-4a71-8b5e-e5d1be5523c9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type chart Gens mem 8cd9915ac670: P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type chart Gens mem 8cd9915ac670
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type chart Gens mem 8cd9915ac670 construction uses the P2 M Ground Theory Heights  Heights Kleiman Ample Ring Finite Type chart Gens mem 8cd9915ac670 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PAmpleRingFiniteType.lean#L39-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFiniteType
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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartGens_mem_8cd9915ac670 (J : Chart x) : ∀ y ∈ chartGens J, y ∈ chartRing S x J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«AmpleRingFiniteType».«chartGens_mem» := P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartGens_mem_8cd9915ac670
