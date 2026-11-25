-- Prove2me | Theorems.Thm_PI_AprimeInfG_tube_ratio
-- name    : PI.AprimeInfG.tube_ratio
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:28:16.708711+00:00
-- url     : https://prove2.me/theorems/11dcb505-854b-40d4-86da-fb3894fde1ef
-- title:
--   Aprime Inf G: tube ratio
-- statement:
--   The Aprime Inf G construction uses the tube ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpTube.lean#L232-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpTube.lean#L232-L289

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Topology Filter Metric Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem PI.AprimeInfG.tube_ratio (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G) (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (hν0 : ν univ ≠ 0) (hνf : ν univ ≠ ∞) {ι η : Type} [Fintype ι] [Fintype η]
    {κ : EuclideanSpace ℝ ι → G} {χ : EuclideanSpace ℝ η → H} {r0 : ℝ} {d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ}
    {e : EuclideanSpace ℝ η → ℝ} (hC : TubeChart μ H ν κ χ r0 d e) (hd : ContinuousAt d 0) (hd0 : 0 < d 0)
    (he : ContinuousAt e 0) (he0 : 0 < e 0) :
    (∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ0 → MeasurableSet (tubeS H (κ '' ball 0 ρ) univ) ∧
      0 < μ (tubeS H (κ '' ball 0 ρ) univ) ∧ μ (tubeS H (κ '' ball 0 ρ) univ) < ⊤) ∧
    Tendsto (fun ρ => (μ (tubeS H (κ '' ball 0 ρ) univ)).toReal / (volume (ball (0 : EuclideanSpace ℝ ι) ρ)).toReal)
      (𝓝[>] 0) (𝓝 (d 0 / e 0 * (ν univ).toReal)) := by sorry
