-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:53:46.433866+00:00
-- url     : https://prove2.me/theorems/39a4f22b-6de3-43fc-bfa8-8721b65f9c53
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone of subset d748224c1d3f: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone of subset d748224c1d3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone of subset d748224c1d3f construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone of subset d748224c1d3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTail.lean#L23-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
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
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f {I : StdCell N} (h : I.1 ⊆ support x) :
    M.cellCone I = locCone M I.1 h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«cellCone_of_subset» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
