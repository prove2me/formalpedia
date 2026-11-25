-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_tate
-- name    : PositivityTheory.ThKG.Loc.Bump.tate
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:04:55.211118+00:00
-- url     : https://prove2.me/theorems/ec2f950a-34ee-5b77-8c26-ebc5992b20a3
-- title:
--   Bump: tate
-- statement:
--   The Bump construction uses the tate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L176-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L176-L273

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]

theorem PositivityTheory.ThKG.Loc.Bump.tate (κ : ι → ℕ) (e : ℕ) (hκ : ∀ w, 2 * e < κ w) : ∃ Z : ℂ, ∀ H : (ι → ℂ) → ℂ, Integrable H →
    Integrable (fun x => H x * r0 κ e x) → Integrable (fun t => FT H t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹)) →
    ∫ t, FT H t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) = Z * ∫ x, H x * r0 κ e x := by sorry
