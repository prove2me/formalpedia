-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_pow_204d807c4e92
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_pow_204d807c4e92
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:49.746979+00:00
-- url     : https://prove2.me/theorems/29874947-a6d3-5414-966d-8ecefaf376bd
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt Is Unit At pow 204d807c4e92: P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt Is Unit At pow 204d807c4e92
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt Is Unit At pow 204d807c4e92 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section Alt Is Unit At pow 204d807c4e92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PClosedPointUnitSection.lean#L136-L139

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
omit [Fintype T]

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_pow_204d807c4e92 {P : HeightOneSpectrum (𝓞 K')} {a : ℕ} {g : K'} (hg : IsUnitAt y P a g) (n : ℕ) :
    IsUnitAt y P (a * n) (g ^ n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSectionAlt».«IsUnitAt».«pow» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_IsUnitAt_pow_204d807c4e92
