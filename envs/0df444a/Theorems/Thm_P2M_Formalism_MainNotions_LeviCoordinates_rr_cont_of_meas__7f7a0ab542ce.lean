-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_LeviCoordinates_rr_cont_of_meas__7f7a0ab542ce
-- name    : P2M_Formalism_MainNotions_LeviCoordinates_rr_cont_of_meas__7f7a0ab542ce
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:58.443952+00:00
-- url     : https://prove2.me/theorems/5ffbe471-6556-4280-a396-0cef82b5fd0a
-- title:
--   P2 M Formalism Main Notions Levi Coordinates rr cont of meas  7f7a0ab542ce: P2 M Formalism Main Notions Levi Coordinates rr cont of meas  7f7a0ab542ce
-- statement:
--   The P2 M Formalism Main Notions Levi Coordinates rr cont of meas  7f7a0ab542ce construction uses the P2 M Formalism Main Notions Levi Coordinates rr cont of meas  7f7a0ab542ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L255-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrdStronglyMeasurable.lean#L255-L334

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
variable {π : G → (H →L[ℂ] H)}

theorem P2M_Formalism_MainNotions_LeviCoordinates_rr_cont_of_meas__7f7a0ab542ce [SigmaFinite μ] [IsLocallyFiniteMeasure μ] (hμ : μ ≠ 0)
    (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ) (x : H) : Continuous fun g => π g x := by sorry

alias «Formalism».«MainNotions».«LeviCoordinates».«rr_cont_of_meas'» := P2M_Formalism_MainNotions_LeviCoordinates_rr_cont_of_meas__7f7a0ab542ce
