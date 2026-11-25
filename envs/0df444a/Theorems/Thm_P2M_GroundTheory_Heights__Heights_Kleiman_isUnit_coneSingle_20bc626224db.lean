-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_coneSingle_20bc626224db
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_coneSingle_20bc626224db
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:02:01.761238+00:00
-- url     : https://prove2.me/theorems/658a3eda-5448-5aab-9dfe-38e73c0b344b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Unit cone Single 20bc626224db: P2 M Ground Theory Heights  Heights Kleiman is Unit cone Single 20bc626224db
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Unit cone Single 20bc626224db construction uses the P2 M Ground Theory Heights  Heights Kleiman is Unit cone Single 20bc626224db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailCone.lean#L123-L128

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
variable (S x)
variable {S x}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_coneSingle_20bc626224db (c : ℤ) {a : Ω} (ha : a ≠ 0) : IsUnit (coneSingle S x c a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isUnit_coneSingle» := P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_coneSingle_20bc626224db
