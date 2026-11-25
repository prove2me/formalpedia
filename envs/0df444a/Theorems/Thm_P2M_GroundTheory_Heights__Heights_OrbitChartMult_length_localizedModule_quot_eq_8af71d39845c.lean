-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_localizedModule_quot_eq_8af71d39845c
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_localizedModule_quot_eq_8af71d39845c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:32.70658+00:00
-- url     : https://prove2.me/theorems/2929179e-3e17-5ec8-8cda-1fecb94928f3
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult length localized Module quot eq 8af71d39845c: P2 M Ground Theory Heights  Heights Orbit Chart Mult length localized Module quot eq 8af71d39845c
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult length localized Module quot eq 8af71d39845c construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult length localized Module quot eq 8af71d39845c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L227-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L227-L299

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {R B : Type*} [CommRing R] [CommRing B]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_localizedModule_quot_eq_8af71d39845c (β : R →+* B) (V W : Ideal R) [hVp : V.IsPrime] (s : R)
    (hker : ∀ F, β F = 0 ↔ F ∈ W) (hunit : ∀ t : V.primeCompl, IsUnit (β t))
    (hgood : ∀ b, ∃ F t, t ∉ V ∧ β t * b = β F) :
    Module.length (Localization.AtPrime V) (LocalizedModule V.primeCompl (R ⧸ (W ⊔ Ideal.span {s}))) =
      Module.length B (B ⧸ Ideal.span {β s}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«length_localizedModule_quot_eq» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_length_localizedModule_quot_eq_8af71d39845c
