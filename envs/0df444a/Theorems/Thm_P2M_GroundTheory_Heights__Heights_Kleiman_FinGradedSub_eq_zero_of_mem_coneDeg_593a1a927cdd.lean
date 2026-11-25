-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_zero_of_mem_coneDeg_593a1a927cdd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_zero_of_mem_coneDeg_593a1a927cdd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:29.863458+00:00
-- url     : https://prove2.me/theorems/a7b9a235-522e-424b-ade1-0b0e45cd3b1c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub eq zero of mem cone Deg 593a1a927cdd: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub eq zero of mem cone Deg 593a1a927cdd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub eq zero of mem cone Deg 593a1a927cdd construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub eq zero of mem cone Deg 593a1a927cdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L91-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
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
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_zero_of_mem_coneDeg_593a1a927cdd {I : StdCell N} (hI : ¬ I.1 ⊆ support x) {y : ConeLaurent S x}
    (hy : y ∈ M.coneDeg c I) : y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«eq_zero_of_mem_coneDeg» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_eq_zero_of_mem_coneDeg_593a1a927cdd
