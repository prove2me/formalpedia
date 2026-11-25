-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_map_C_mem_monos_b5180478af36
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_map_C_mem_monos_b5180478af36
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:57.426808+00:00
-- url     : https://prove2.me/theorems/dd84e862-834d-5a4f-9ab9-aa3d3c9ea2a4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman map C mem monos b5180478af36: P2 M Ground Theory Heights  Heights Kleiman map C mem monos b5180478af36
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman map C mem monos b5180478af36 construction uses the P2 M Ground Theory Heights  Heights Kleiman map C mem monos b5180478af36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L18-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
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
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_map_C_mem_monos_b5180478af36 {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    MvPolynomial.map (C : S →+* MvPolynomial (Fin (r + 1)) S) s ∈ monos (S := MvPolynomial (Fin (r + 1)) S) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«map_C_mem_monos» := P2M_GroundTheory_Heights__Heights_Kleiman_map_C_mem_monos_b5180478af36
