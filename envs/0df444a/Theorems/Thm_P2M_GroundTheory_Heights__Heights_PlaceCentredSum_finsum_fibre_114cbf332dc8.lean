-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlaceCentredSum_finsum_fibre_114cbf332dc8
-- name    : P2M_GroundTheory_Heights__Heights_PlaceCentredSum_finsum_fibre_114cbf332dc8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:55.158088+00:00
-- url     : https://prove2.me/theorems/adcb743a-6c84-47b2-bdbf-6075da4ed876
-- title:
--   P2 M Ground Theory Heights  Heights Place Centred Sum finsum fibre 114cbf332dc8: P2 M Ground Theory Heights  Heights Place Centred Sum finsum fibre 114cbf332dc8
-- statement:
--   The P2 M Ground Theory Heights  Heights Place Centred Sum finsum fibre 114cbf332dc8 construction uses the P2 M Ground Theory Heights  Heights Place Centred Sum finsum fibre 114cbf332dc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L90-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPlaceCentredSum.lean#L90-L111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField IsDedekindDomain Ideal
open GroundTheory.Heights₂.Heights.PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]

theorem P2M_GroundTheory_Heights__Heights_PlaceCentredSum_finsum_fibre_114cbf332dc8 {α β : Type*} (π : α → β) [∀ b, Fintype {a // π a = b}] (n : α → ℕ) (N : ℕ)
    (g : β → ℝ) (hg : g.support.Finite) (hsum : ∀ b, ∑ a : {a // π a = b}, n a.1 = N) :
    ∑ᶠ a, (n a : ℝ) * g (π a) = N * ∑ᶠ b, g b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PlaceCentredSum».«finsum_fibre» := P2M_GroundTheory_Heights__Heights_PlaceCentredSum_finsum_fibre_114cbf332dc8
