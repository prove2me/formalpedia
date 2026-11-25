-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coneLaurent_smul_a6c484f2d236
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coneLaurent_smul_a6c484f2d236
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:12:17.277996+00:00
-- url     : https://prove2.me/theorems/d400611e-8c57-4ed1-9281-55ca2e98adfe
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman cone Laurent smul a6c484f2d236: P2 M Ground Theory Heights  Heights Kleiman cone Laurent smul a6c484f2d236
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman cone Laurent smul a6c484f2d236 construction uses the P2 M Ground Theory Heights  Heights Kleiman cone Laurent smul a6c484f2d236 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L50-L50

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coneLaurent_smul_a6c484f2d236 (p : Poly S N) (w : ConeLaurent S x) : p • w = coneLaurent S x p * w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coneLaurent_smul» := P2M_GroundTheory_Heights__Heights_Kleiman_coneLaurent_smul_a6c484f2d236
