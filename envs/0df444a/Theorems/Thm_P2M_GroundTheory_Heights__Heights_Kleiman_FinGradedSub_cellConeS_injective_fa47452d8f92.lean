-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_injective_fa47452d8f92
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_injective_fa47452d8f92
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:51.844213+00:00
-- url     : https://prove2.me/theorems/6a33d191-17ac-5ff5-936c-a1371f4ab17c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone S injective fa47452d8f92: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone S injective fa47452d8f92
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone S injective fa47452d8f92 construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone S injective fa47452d8f92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L47-L57

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_injective_fa47452d8f92 (I : StdCell N) : Function.Injective (M.cellConeS I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«cellConeS_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_injective_fa47452d8f92
