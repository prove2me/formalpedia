-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quot_succ_le_e09e019fe7e4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quot_succ_le_e09e019fe7e4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:02:29.479588+00:00
-- url     : https://prove2.me/theorems/d6cd1944-4dfe-40a2-b570-bb71370d0a4c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ring Krull Dim quot succ le e09e019fe7e4: P2 M Ground Theory Heights  Heights Kleiman ring Krull Dim quot succ le e09e019fe7e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ring Krull Dim quot succ le e09e019fe7e4 construction uses the P2 M Ground Theory Heights  Heights Kleiman ring Krull Dim quot succ le e09e019fe7e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L50-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCycleSplit
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
open MvPolynomial Filter
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quot_succ_le_e09e019fe7e4 {G pp : Ideal (Poly S N)} [G.IsPrime] (hle : G ≤ pp) {f : Poly S N}
    (hfp : f ∈ pp) (hfG : f ∉ G) : ringKrullDim (Poly S N ⧸ pp) + 1 ≤ ringKrullDim (Poly S N ⧸ G) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ringKrullDim_quot_succ_le» := P2M_GroundTheory_Heights__Heights_Kleiman_ringKrullDim_quot_succ_le_e09e019fe7e4
