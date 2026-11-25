-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_zero_subsingleton_fd8caf63e24d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_zero_subsingleton_fd8caf63e24d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:31.99285+00:00
-- url     : https://prove2.me/theorems/f13b0399-d4bf-4e9b-bb72-57287f8d5204
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel cell zero subsingleton fd8caf63e24d: P2 M Ground Theory Heights  Heights Hilbert Samuel cell zero subsingleton fd8caf63e24d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel cell zero subsingleton fd8caf63e24d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel cell zero subsingleton fd8caf63e24d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/GeneratedModOfSubsingleton.lean#L34-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsKleimanScheme
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]
omit [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_zero_subsingleton_fd8caf63e24d : Subsingleton (KH.Cell K ι 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«cell_zero_subsingleton» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_cell_zero_subsingleton_fd8caf63e24d
