-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_not_4e0646e9c831
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_not_4e0646e9c831
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:39.10203+00:00
-- url     : https://prove2.me/theorems/742b6910-0a0c-404a-b0ff-4cc74c6f08aa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone of not 4e0646e9c831: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone of not 4e0646e9c831
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone of not 4e0646e9c831 construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone of not 4e0646e9c831 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L44-L45

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_not_4e0646e9c831 {I : StdCell N} (h : ¬ I.1 ⊆ support x) : M.cellCone I = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«cellCone_of_not» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_not_4e0646e9c831
