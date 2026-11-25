-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_res_bcc5079ec5bf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_res_bcc5079ec5bf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:28.555877+00:00
-- url     : https://prove2.me/theorems/61e7a12d-cac0-481f-bd8c-9876de4c7fb5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone S res bcc5079ec5bf: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone S res bcc5079ec5bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone S res bcc5079ec5bf construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub cell Cone S res bcc5079ec5bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L59-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L59-L69

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_res_bcc5079ec5bf (I J : StdCell N) (h : I.1 ⊆ J.1) (m : LocMod S N M.coneSub I.1) :
    M.cellConeS J (locResS I J h m) = supportRes S x I J h (M.cellConeS I m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«cellConeS_res» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_res_bcc5079ec5bf
