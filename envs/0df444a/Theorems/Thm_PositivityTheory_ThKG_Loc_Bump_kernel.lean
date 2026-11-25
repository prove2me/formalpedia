-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_kernel
-- name    : PositivityTheory.ThKG.Loc.Bump.kernel
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:04:35.840981+00:00
-- url     : https://prove2.me/theorems/9bc63866-f684-51b7-98e9-7d43ed339d3b
-- title:
--   Bump: kernel
-- statement:
--   The Bump construction uses the kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L49-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/IntegrableConjPowGaussian.lean#L49-L67

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

theorem PositivityTheory.ThKG.Loc.Bump.kernel {a j : (ι → ℂ) → ℂ} (ha : AEStronglyMeasurable a volume) (hj : Integrable j) (hjm : Measurable j) {s : (ι → ℂ) → ι → ℂ}
    (hs : Measurable s) (hsU : ∀ x, (∀ w, x w ≠ 0) → ∀ w, s x w ≠ 0) (hi : Integrable fun x => a x * ((nm (s x) : ℝ) : ℂ)⁻¹) :
    Integrable (fun q : (ι → ℂ) × (ι → ℂ) => a q.1 * j (s q.1 * q.2)) (volume.prod volume) ∧
      ∫ x, ∫ y, a x * j (s x * y) = (∫ x, a x * ((nm (s x) : ℝ) : ℂ)⁻¹) * ∫ y, j y := by sorry
