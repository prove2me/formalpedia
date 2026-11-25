-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_degZ_add_18174cc39b3c
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_degZ_add_18174cc39b3c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:27.026364+00:00
-- url     : https://prove2.me/theorems/01aa1523-8712-4b69-b242-e2c0f0f20a01
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration deg Z add 18174cc39b3c: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration deg Z add 18174cc39b3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration deg Z add 18174cc39b3c construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration deg Z add 18174cc39b3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L22-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_degZ_add_18174cc39b3c (b b' : K → ℕ) : degZ (b + b') = degZ b + degZ b' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«degZ_add» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_degZ_add_18174cc39b3c
