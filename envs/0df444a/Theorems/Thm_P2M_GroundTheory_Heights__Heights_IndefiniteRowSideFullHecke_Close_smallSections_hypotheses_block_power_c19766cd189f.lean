-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_smallSections_hypotheses_block_power_c19766cd189f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_smallSections_hypotheses_block_power_c19766cd189f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:15:43.516343+00:00
-- url     : https://prove2.me/theorems/f582a18b-7eda-54ec-aa26-72729ba7d817
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close small Sections hypotheses block power c19766cd189f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close sm
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close small Sections hypotheses block power c19766cd189f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close small Sections hypotheses block power c19766cd189f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L372-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/SectionInjectivityHypothesesProjectiveLine.lean#L372-L380

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open AddBlockData
variable (n)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_smallSections_hypotheses_block_power_c19766cd189f (k₀ : ι) :
    (MvPolynomial.IsHomogeneous (1 : MvPolynomial (Fin ((powBlock n k₀ 1).m + 1)) ℤ) 0) ∧
    (∀ w ∈ conePoints (powBlock n k₀ 1).ext ℂ,
      ‖eval₂ (Int.castRingHom ℂ) (newPart w) (1 : MvPolynomial (Fin ((powBlock n k₀ 1).m + 1)) ℤ)‖ ≤
        hPlus (powChartForms n k₀ 1) (wholeGens n) (blockPowLine n k₀ 1) w ^ 0) ∧
    val (ArithVariety.whole n) 1 =
      aeval (powBlock n k₀ 1).x (1 : MvPolynomial (Fin ((powBlock n k₀ 1).m + 1)) ℤ) *
        val (ArithVariety.whole n) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«smallSections_hypotheses_block_power» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_smallSections_hypotheses_block_power_c19766cd189f
