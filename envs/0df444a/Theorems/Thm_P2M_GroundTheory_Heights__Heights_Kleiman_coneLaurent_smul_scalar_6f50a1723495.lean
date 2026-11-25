-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coneLaurent_smul_scalar_6f50a1723495
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coneLaurent_smul_scalar_6f50a1723495
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:12.807417+00:00
-- url     : https://prove2.me/theorems/557051f3-6853-5406-b811-394ae68a0b37
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cone Laurent smul scalar 6f50a1723495: P2 M Ground Theory Heights  Heights Kleiman cone Laurent smul scalar 6f50a1723495
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cone Laurent smul scalar 6f50a1723495 construction uses the P2 M Ground Theory Heights  Heights Kleiman cone Laurent smul scalar 6f50a1723495 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L52-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
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
variable (S : Type u) [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable (x : Fin (N + 1) → Ω)
variable {S x}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coneLaurent_smul_scalar_6f50a1723495 (s : S) (w : ConeLaurent S x) :
    s • w = algebraMap S (Poly S N) s • w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coneLaurent_smul_scalar» := P2M_GroundTheory_Heights__Heights_Kleiman_coneLaurent_smul_scalar_6f50a1723495
