-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_map_78062567800a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_map_78062567800a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:07:20.795422+00:00
-- url     : https://prove2.me/theorems/978d0c97-f042-52fb-a19d-1d5f5b186529
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists monos map 78062567800a: P2 M Ground Theory Heights  Heights Kleiman exists monos map 78062567800a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists monos map 78062567800a construction uses the P2 M Ground Theory Heights  Heights Kleiman exists monos map 78062567800a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFiniteSections.lean#L78-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
  [IsFractionRing S F]
omit [IsFractionRing S F]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_map_78062567800a {I : Finset (Fin (N + 1))} {s : Poly F N} (hs : s ∈ monos I) :
    ∃ s' : Poly S N, s' ∈ monos I ∧ map (algebraMap S F) s' = s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_monos_map» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_map_78062567800a
